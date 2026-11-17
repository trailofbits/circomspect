use std::collections::{BTreeMap, BTreeSet};
use std::time::Duration;

use parser::hir::LiftedProject;
use parser::frontend::{DiagnosticKind, Item, LoadedProject, Span};
use program_structure::report::Report;
use program_structure::report_code::ReportCode;

use crate::application::coverage::{CoverageExplanation, CoverageKind};
use crate::application::grouping::{ContextDisplay, ReportGroups};
use crate::application::{AnalysisObserver, ApplicationError};
use crate::interprocedural::ContextEvidence;
use crate::rules::{RenderError, SourceMap};

#[cfg(test)]
mod tests;

fn syntax_comment(kind: DiagnosticKind) -> &'static str {
    match kind {
        DiagnosticKind::UnsupportedVersion => "This Circom version is unsupported.",
        DiagnosticKind::FeatureVersion => "This syntax requires another Circom version.",
        DiagnosticKind::InvalidToken => "This token is invalid.",
        DiagnosticKind::UnterminatedString => "This string literal is unterminated.",
        DiagnosticKind::UnterminatedComment => "This block comment is unterminated.",
        DiagnosticKind::InvalidNumber => "This numeric literal is invalid.",
        DiagnosticKind::Syntax => "This syntax is invalid.",
        DiagnosticKind::MissingInclude => "This include cannot be resolved.",
        DiagnosticKind::CyclicInclude => "This include creates a cycle.",
        DiagnosticKind::FileRead => "This file could not be read.",
    }
}

pub(super) struct Diagnostics<'a, 'b> {
    sources: &'a SourceMap<'b>,
    reports: ReportGroups,
    incomplete: BTreeMap<ScopeKey, IncompleteScope>,
    timeouts: Vec<Report>,
    emitted_timeouts: usize,
}

impl<'a, 'b> Diagnostics<'a, 'b> {
    pub(super) fn new(sources: &'a SourceMap<'b>) -> Self {
        Self {
            sources,
            reports: ReportGroups::default(),
            incomplete: BTreeMap::new(),
            timeouts: Vec::new(),
            emitted_timeouts: 0,
        }
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
                self.locate(&mut report, span, syntax_comment(diagnostic.kind).into())?;
            }
            self.reports.insert_source(report);
        }
        self.main_diagnostics(lifted)?;
        for diagnostic in &lifted.diagnostics {
            self.reports.insert_source(self.sources.semantic_report(diagnostic)?);
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
                    report.add_primary(
                        0..0,
                        file,
                        "This file has no Circom version pragma.".to_string(),
                    );
                }
                self.reports.insert_source(report);
            }
        }
        Ok(())
    }

    fn main_diagnostics(&mut self, lifted: &LiftedProject) -> Result<(), RenderError> {
        let mut seen = Vec::new();
        for main in lifted.hir.mains() {
            let current_is_root = self
                .sources
                .file_id(main.span.source())
                .is_some_and(|file| self.sources.files().user_inputs().contains(&file));
            let independent_roots = current_is_root
                && seen.iter().all(|previous: &&parser::hir::Main| {
                    previous.span.source() != main.span.source()
                        && self
                            .sources
                            .file_id(previous.span.source())
                            .is_some_and(|file| self.sources.files().user_inputs().contains(&file))
                });
            if seen.is_empty() || independent_roots {
                seen.push(main);
                continue;
            }
            let first = seen
                .iter()
                .find(|previous| previous.span.source() == main.span.source())
                .copied()
                .unwrap_or(seen[0]);
            seen.push(main);
            let mut report = Report::error(
                "Multiple main components are defined.".into(),
                ReportCode::MultipleMainInComponent,
            );
            self.locate(&mut report, main.span, "This is an additional main component.".into())?;
            let (file, range) = self.sources.location(first.span)?;
            report.add_secondary(range, file, Some("This is the first main component.".into()));
            self.reports.insert_source(report);
        }
        Ok(())
    }

    pub(super) fn push(&mut self, report: Report) {
        self.reports.insert_source(report);
    }

    pub(super) fn timed_out(&mut self, name: &str, kind: &str, limit: Duration) {
        let report = Report::warning(
            format!("Analysis of the '{name}' {kind} timed out after {} seconds.", limit.as_secs()),
            ReportCode::AnalysisTimeout,
        );
        self.timeouts.push(report);
    }

    pub(super) fn source_incomplete(&mut self, explanation: CoverageExplanation) {
        let span = explanation.span;
        let key =
            ScopeKey::Source(span.source().index(), span.start(), span.end(), explanation.kind);
        self.incomplete.entry(key).or_insert_with(|| IncompleteScope::new(span)).add(explanation);
    }

    pub(super) fn scope_incomplete(
        &mut self,
        evidence: &ContextEvidence,
        name: Span,
        explanations: Vec<CoverageExplanation>,
    ) {
        for explanation in explanations {
            let span = explanation.span;
            let source_key =
                ScopeKey::Source(span.source().index(), span.start(), span.end(), explanation.kind);
            if let Some(source) = self.incomplete.get_mut(&source_key) {
                if source.has_cause(&explanation) {
                    source.add(explanation);
                    continue;
                }
            }
            self.incomplete
                .entry(ScopeKey::Context(evidence.clone(), explanation.kind))
                .or_insert_with(|| IncompleteScope::new(name))
                .add(explanation);
        }
    }

    fn locate(&self, report: &mut Report, span: Span, label: String) -> Result<(), RenderError> {
        let (file, range) = self.sources.location(span)?;
        report.add_primary(range, file, label);
        Ok(())
    }

    pub(super) fn emit_new(
        &mut self,
        observer: &mut dyn AnalysisObserver,
    ) -> Result<(), ApplicationError> {
        self.reports.emit_new(self.sources, observer)?;
        for report in &self.timeouts[self.emitted_timeouts..] {
            observer.report(report, self.sources.files())?;
            self.emitted_timeouts += 1;
        }
        Ok(())
    }

    pub(super) fn finish(
        mut self,
        observer: &mut dyn AnalysisObserver,
    ) -> Result<Vec<Report>, ApplicationError> {
        for (key, scope) in &self.incomplete {
            let mut report = coverage_report(key.kind());
            self.locate(
                &mut report,
                scope.primary,
                "Some checks could not be completed here.".into(),
            )?;
            let mut help = BTreeSet::new();
            for (key, span) in &scope.details {
                let (file, range) = self.sources.location(*span)?;
                report.add_secondary(range, file, Some(key.message.clone()));
                help.insert(&key.help);
            }
            for action in help {
                report.add_note(format!("Help: {action}"));
            }
            match key {
                ScopeKey::Context(_, _) => self.reports.insert(report, ContextDisplay::Omit),
                ScopeKey::Source(_, _, _, _) => {
                    self.reports.insert_source(report);
                }
            }
        }
        let mut reports = self.reports.finish(self.sources, observer)?;
        reports.append(&mut self.timeouts);
        Ok(reports)
    }
}

fn coverage_report(kind: CoverageKind) -> Report {
    match kind {
        CoverageKind::MissingContext => Report::info(
            "Some checks need additional context.".into(),
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

struct IncompleteScope {
    primary: Span,
    details: BTreeMap<DetailKey, Span>,
}

impl IncompleteScope {
    fn new(primary: Span) -> Self {
        Self { primary, details: BTreeMap::new() }
    }

    fn has_cause(&self, explanation: &CoverageExplanation) -> bool {
        self.details
            .keys()
            .any(|key| key.message == explanation.message && key.help == explanation.help)
    }

    fn add(&mut self, explanation: CoverageExplanation) {
        let span = explanation.span;
        let key = DetailKey {
            source: span.source().index(),
            start: span.start(),
            end: span.end(),
            message: explanation.message,
            help: explanation.help,
        };
        self.details.entry(key).or_insert(span);
    }
}
