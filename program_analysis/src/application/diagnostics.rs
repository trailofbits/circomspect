use std::collections::{BTreeMap, BTreeSet};

use parser::hir::LiftedProject;
use parser::frontend::{DiagnosticKind, Item, LoadedProject, Span};
use program_structure::report::Report;
use program_structure::report_code::ReportCode;

use crate::application::coverage::{check_name, CoverageContext, CoverageExplanation, CoverageKind};
use crate::application::grouping::ReportGroups;
use crate::interprocedural::ContextEvidence;
use crate::rules::{RenderError, RuleKind, SourceMap};

#[cfg(test)]
mod tests;

pub(super) struct Diagnostics<'a, 'b> {
    sources: &'a SourceMap<'b>,
    reports: ReportGroups,
    incomplete: BTreeMap<ScopeKey, IncompleteScope>,
}

impl<'a, 'b> Diagnostics<'a, 'b> {
    pub(super) fn new(sources: &'a SourceMap<'b>) -> Self {
        Self { sources, reports: ReportGroups::default(), incomplete: BTreeMap::new() }
    }

    pub(super) fn frontend(
        &mut self,
        loaded: &LoadedProject,
        lifted: &LiftedProject,
    ) -> Result<(), RenderError> {
        for diagnostic in &lifted.syntax_diagnostics {
            let code = match diagnostic.kind {
                DiagnosticKind::UnsupportedVersion | DiagnosticKind::FeatureVersion => {
                    ReportCode::CompilerVersionError
                }
                DiagnosticKind::InvalidToken
                | DiagnosticKind::UnterminatedString
                | DiagnosticKind::UnterminatedComment
                | DiagnosticKind::InvalidNumber
                | DiagnosticKind::Syntax
                | DiagnosticKind::MissingInclude
                | DiagnosticKind::CyclicInclude
                | DiagnosticKind::FileRead => ReportCode::ParseFail,
            };
            let mut report = Report::error(diagnostic.message.clone(), code);
            if let Some(span) = diagnostic.span() {
                self.locate(&mut report, span, diagnostic.message.clone())?;
            }
            self.reports.insert_source(report);
        }
        self.main_diagnostics(lifted)?;
        for diagnostic in &lifted.diagnostics {
            self.reports.insert_source(self.sources.semantic_report(diagnostic)?);
        }
        for region in &lifted.incomplete {
            let Some(span) = region.span() else { continue };
            let coverage = CoverageContext { hir: &lifted.hir, facts: None, evidence: None, span };
            for explanation in coverage.source(&region.reason) {
                self.source_incomplete(explanation);
            }
        }
        for source in &loaded.files {
            let versioned = source.outcome.ast.items.iter().any(|item| {
                if let Item::Pragma { pragma, .. } = item {
                    return match pragma {
                        parser::frontend::Pragma::Version(_) => true,
                        parser::frontend::Pragma::CustomTemplates => false,
                    };
                }
                false
            });
            if !versioned && source.outcome.diagnostics.is_empty() {
                let mut report = Report::warning(
                    "No compiler version is specified; analyzing as Circom 2.2.3.".to_string(),
                    ReportCode::NoCompilerVersionWarning,
                );
                if let Some(file) = self.sources.file_id(source.id) {
                    report.add_primary(0..0, file, "Add `pragma circom 2.2.3;`.".to_string());
                }
                self.reports.insert_source(report);
            }
        }
        Ok(())
    }

    fn main_diagnostics(&mut self, lifted: &LiftedProject) -> Result<(), RenderError> {
        let Some(first) = lifted.hir.mains().first() else { return Ok(()) };
        for main in lifted.hir.mains().iter().skip(1) {
            let mut report = Report::error(
                "Multiple main components are defined.".into(),
                ReportCode::MultipleMainInComponent,
            );
            self.locate(&mut report, main.span, "Additional main component.".into())?;
            let (file, range) = self.sources.location(first.span)?;
            report.add_secondary(range, file, Some("First main component.".into()));
            self.reports.insert_source(report);
        }
        Ok(())
    }

    pub(super) fn push(&mut self, report: Report) {
        self.reports.insert_source(report);
    }

    pub(super) fn source_incomplete(&mut self, explanation: CoverageExplanation) {
        let span = explanation.span;
        let key =
            ScopeKey::Source(span.source().index(), span.start(), span.end(), explanation.kind);
        self.incomplete
            .entry(key)
            .or_insert_with(|| IncompleteScope::new(span))
            .add(explanation, None);
    }

    pub(super) fn scope_incomplete(
        &mut self,
        evidence: &ContextEvidence,
        name: Span,
        explanations: Vec<CoverageExplanation>,
        rule: Option<RuleKind>,
    ) {
        for explanation in explanations {
            let span = explanation.span;
            let source_key =
                ScopeKey::Source(span.source().index(), span.start(), span.end(), explanation.kind);
            if let Some(source) = self.incomplete.get_mut(&source_key) {
                if source.has_cause(&explanation) {
                    source.add(explanation, rule);
                    source.contexts.insert(evidence.clone());
                    continue;
                }
            }
            self.incomplete
                .entry(ScopeKey::Context(evidence.clone(), explanation.kind))
                .or_insert_with(|| IncompleteScope::new(name))
                .add(explanation, rule);
        }
    }

    fn locate(&self, report: &mut Report, span: Span, label: String) -> Result<(), RenderError> {
        let (file, range) = self.sources.location(span)?;
        report.add_primary(range, file, label);
        Ok(())
    }

    pub(super) fn finish(mut self) -> Result<Vec<Report>, RenderError> {
        for (key, scope) in &self.incomplete {
            let mut report = coverage_report(key.kind());
            self.locate(
                &mut report,
                scope.primary,
                "Some checks could not be completed here.".into(),
            )?;
            let mut help = BTreeSet::new();
            for (key, label) in &scope.details {
                let (file, range) = self.sources.location(label.span)?;
                let mut checks = Vec::new();
                for kind in &label.rules {
                    checks.push(format!("{} ({})", check_name(*kind), kind.code().id()));
                }
                let message = if checks.is_empty() {
                    key.message.clone()
                } else {
                    format!("{}: {}", checks.join(", "), key.message)
                };
                report.add_secondary(range, file, Some(message));
                help.insert(&key.help);
            }
            for action in help {
                report.add_note(format!("Help: {action}"));
            }
            match key {
                ScopeKey::Context(evidence, _) => self.reports.insert(report, evidence),
                ScopeKey::Source(_, _, _, _) => {
                    self.reports.insert_source(report.clone());
                    for evidence in &scope.contexts {
                        self.reports.insert(report.clone(), evidence);
                    }
                }
            }
        }
        self.reports.finish(self.sources)
    }
}

fn coverage_report(kind: CoverageKind) -> Report {
    match kind {
        CoverageKind::MissingContext => Report::info(
            "Some checks need additional context.".into(),
            ReportCode::IncompleteCoverage,
        ),
        CoverageKind::Unsupported => Report::warning(
            "Some checks are not supported for this code.".into(),
            ReportCode::IncompleteCoverage,
        ),
        CoverageKind::ResourceLimit => Report::warning(
            "Some checks reached an analysis limit.".into(),
            ReportCode::IncompleteCoverage,
        ),
        CoverageKind::InternalError => Report::error(
            "Analysis could not complete due to an internal error.".into(),
            ReportCode::RuntimeError,
        ),
    }
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
enum ScopeKey {
    Source(usize, usize, usize, CoverageKind),
    Context(ContextEvidence, CoverageKind),
}

impl ScopeKey {
    fn kind(&self) -> CoverageKind {
        match self {
            Self::Source(_, _, _, kind) | Self::Context(_, kind) => *kind,
        }
    }
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
struct DetailKey {
    source: usize,
    start: usize,
    end: usize,
    message: String,
    help: String,
}

struct IncompleteLabel {
    span: Span,
    rules: BTreeSet<RuleKind>,
}

struct IncompleteScope {
    primary: Span,
    details: BTreeMap<DetailKey, IncompleteLabel>,
    contexts: BTreeSet<ContextEvidence>,
}

impl IncompleteScope {
    fn new(primary: Span) -> Self {
        Self { primary, details: BTreeMap::new(), contexts: BTreeSet::new() }
    }

    fn has_cause(&self, explanation: &CoverageExplanation) -> bool {
        self.details
            .keys()
            .any(|key| key.message == explanation.message && key.help == explanation.help)
    }

    fn add(&mut self, explanation: CoverageExplanation, rule: Option<RuleKind>) {
        let span = explanation.span;
        let key = DetailKey {
            source: span.source().index(),
            start: span.start(),
            end: span.end(),
            message: explanation.message,
            help: explanation.help,
        };
        let label = self
            .details
            .entry(key)
            .or_insert_with(|| IncompleteLabel { span, rules: BTreeSet::new() });
        if let Some(rule) = rule {
            label.rules.insert(rule);
        }
    }
}
