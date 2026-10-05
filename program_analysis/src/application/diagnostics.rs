use std::collections::{BTreeMap, BTreeSet};

use parser::hir::{IncompleteReason, LiftedProject};
use parser::new_frontend::{DiagnosticKind, Item, LoadedProject, Span};
use program_structure::report::Report;
use program_structure::report_code::ReportCode;

use crate::interprocedural::{ContextEvidence, SummaryBlocker};
use crate::new_rules::{AbstentionReason, RenderError, RuleKind, SourceMap};

pub(super) struct Diagnostics<'a, 'b> {
    sources: &'a SourceMap<'b>,
    reports: Vec<Report>,
    incomplete: BTreeMap<ScopeKey, IncompleteScope>,
    source_regions: Vec<(Span, String)>,
    attached_regions: BTreeSet<usize>,
}

impl<'a, 'b> Diagnostics<'a, 'b> {
    pub(super) fn new(sources: &'a SourceMap<'b>) -> Self {
        Self {
            sources,
            reports: Vec::new(),
            incomplete: BTreeMap::new(),
            source_regions: Vec::new(),
            attached_regions: BTreeSet::new(),
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
                self.locate(&mut report, span, diagnostic.message.clone())?;
            }
            self.reports.push(report);
        }
        self.main_diagnostics(lifted)?;
        for diagnostic in &lifted.diagnostics {
            self.reports.push(self.sources.semantic_report(diagnostic)?);
        }
        for region in &lifted.incomplete {
            if let Some(span) = region.span() {
                self.source_regions.push((span, incomplete_reason(&region.reason).to_owned()));
            }
        }
        for source in &loaded.files {
            let versioned = source.outcome.ast.items.iter().any(|item| {
                if let Item::Pragma { pragma, .. } = item {
                    return match pragma {
                        parser::new_frontend::Pragma::Version(_) => true,
                        parser::new_frontend::Pragma::CustomTemplates => false,
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
                self.reports.push(report);
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
            self.reports.push(report);
        }
        Ok(())
    }

    pub(super) fn push(&mut self, report: Report) {
        self.reports.push(report);
    }

    pub(super) fn source_incomplete(&mut self, span: Span, reason: &str) {
        let key = ScopeKey::Source(span.source().index(), span.start(), span.end());
        self.incomplete.entry(key).or_insert_with(|| IncompleteScope::new(span)).add(
            span,
            IncompleteCause::Source(reason.into()),
            None,
        );
    }

    pub(super) fn begin_scope(&mut self, evidence: &ContextEvidence, name: Span, body: Span) {
        for (index, (span, reason)) in self.source_regions.iter().enumerate() {
            if span.source() == body.source()
                && span.start() >= body.start()
                && span.end() <= body.end()
            {
                self.attached_regions.insert(index);
                self.incomplete
                    .entry(ScopeKey::Context(evidence.clone()))
                    .or_insert_with(|| IncompleteScope::new(name))
                    .add(*span, IncompleteCause::Source(reason.clone()), None);
            }
        }
    }

    pub(super) fn scope_incomplete(
        &mut self,
        evidence: &ContextEvidence,
        name: Span,
        detail: IncompleteDetail,
    ) {
        self.incomplete
            .entry(ScopeKey::Context(evidence.clone()))
            .or_insert_with(|| IncompleteScope::new(name))
            .add(detail.span, detail.reason, detail.rule);
    }

    fn locate(&self, report: &mut Report, span: Span, label: String) -> Result<(), RenderError> {
        let (file, range) = self.sources.location(span)?;
        report.add_primary(range, file, label);
        Ok(())
    }

    pub(super) fn finish(mut self) -> Result<Vec<Report>, RenderError> {
        let regions = std::mem::take(&mut self.source_regions);
        for (index, (span, reason)) in regions.into_iter().enumerate() {
            if !self.attached_regions.contains(&index) {
                self.source_incomplete(span, &reason);
            }
        }
        for (key, scope) in &self.incomplete {
            let mut report = Report::warning(
                "Analysis is incomplete for this source scope.".to_string(),
                ReportCode::IncompleteCoverage,
            );
            self.locate(
                &mut report,
                scope.primary,
                "Some properties could not be certified.".into(),
            )?;
            for (key, label) in &scope.details {
                let (file, range) = self.sources.location(label.span)?;
                let rules: BTreeSet<_> = label.rules.iter().map(|kind| kind.code().id()).collect();
                let message = if rules.is_empty() {
                    key.reason.message().to_owned()
                } else {
                    let rules = rules.into_iter().collect::<Vec<_>>().join(", ");
                    format!("{rules}: {}", key.reason.message())
                };
                report.add_secondary(range, file, Some(message));
            }
            if let ScopeKey::Context(evidence) = key {
                for site in evidence.call_path() {
                    let (file, range) = self.sources.location(site.span())?;
                    report.add_secondary(range, file, Some("Reached through this call.".into()));
                }
            }
            self.reports.push(report);
        }
        Ok(self.reports)
    }
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
enum ScopeKey {
    Source(usize, usize, usize),
    Context(ContextEvidence),
}

pub(super) struct IncompleteDetail {
    pub span: Span,
    pub reason: IncompleteCause,
    pub rule: Option<RuleKind>,
}

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum IncompleteCause {
    Source(String),
    Rule(AbstentionReason),
    Summary(SummaryBlocker),
}

impl IncompleteCause {
    pub(super) fn message(&self) -> &str {
        match self {
            Self::Source(reason) => reason,
            Self::Rule(reason) => abstention_reason(reason),
            Self::Summary(reason) => summary_reason(reason),
        }
    }
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
struct DetailKey {
    source: usize,
    start: usize,
    end: usize,
    reason: IncompleteCause,
}

struct IncompleteLabel {
    span: Span,
    rules: BTreeSet<RuleKind>,
}

struct IncompleteScope {
    primary: Span,
    details: BTreeMap<DetailKey, IncompleteLabel>,
}

impl IncompleteScope {
    fn new(primary: Span) -> Self {
        Self { primary, details: BTreeMap::new() }
    }

    fn add(&mut self, span: Span, reason: IncompleteCause, rule: Option<RuleKind>) {
        let key = DetailKey {
            source: span.source().index(),
            start: span.start(),
            end: span.end(),
            reason,
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

fn incomplete_reason(reason: &IncompleteReason) -> &str {
    match reason {
        IncompleteReason::Syntax => "source contains invalid syntax",
        IncompleteReason::Include => "an included source is unavailable",
        IncompleteReason::MissingReference(_) => "a referenced definition is missing",
        IncompleteReason::AmbiguousReference(_) => "a reference has multiple definitions",
        IncompleteReason::WrongKind(_) => "a referenced definition has the wrong kind",
        IncompleteReason::UnknownType => "a value type is unknown",
        IncompleteReason::UnknownSymbol(_) => "a referenced symbol is missing",
        IncompleteReason::NonCompileTime => "a compile-time value could not be determined",
        IncompleteReason::InvalidAssignment => "an assignment is invalid",
        IncompleteReason::Unsupported(reason) => reason,
    }
}

fn abstention_reason(reason: &AbstentionReason) -> &'static str {
    match reason {
        AbstentionReason::LocalFacts(_) => "the required local facts could not be certified",
        AbstentionReason::Call(_) => "the required call could not be resolved or certified",
        AbstentionReason::Summary(reasons) => {
            if reasons.len() == 1 {
                if let Some(reason) = reasons.first() {
                    return summary_reason(reason);
                }
            }
            "the required call or constraint closure is incomplete"
        }
        AbstentionReason::SymbolicParameters => "the result depends on unknown parameter values",
        AbstentionReason::IncompleteDefinition => {
            "the definition contains unresolved source errors"
        }
        AbstentionReason::UnsupportedConstruct => {
            "the required property is outside supported analysis"
        }
    }
}

fn summary_reason(reason: &SummaryBlocker) -> &'static str {
    match reason {
        SummaryBlocker::IncompleteDefinition => "the definition contains unresolved source errors",
        SummaryBlocker::UnprovenArgument(_) => "a call argument could not be determined",
        SummaryBlocker::UnsupportedCallForm | SummaryBlocker::UnsupportedContext => {
            "the required property is outside supported analysis"
        }
        SummaryBlocker::LocalFacts(_) | SummaryBlocker::LocalAnalysis(_) => {
            "the required local facts could not be certified"
        }
        SummaryBlocker::InvalidAssignment(_) | SummaryBlocker::InvalidValueUse(_) => {
            "an assignment or value use is invalid"
        }
        SummaryBlocker::WrongInstance
        | SummaryBlocker::DuplicateInstance
        | SummaryBlocker::SymbolicInstance => "the exact component instance could not be certified",
        SummaryBlocker::MissingInputBinding
        | SummaryBlocker::DuplicateInputBinding
        | SummaryBlocker::WitnessOnlyInput => "component input constraints could not be certified",
        SummaryBlocker::ExternalSummary => "an external dependency has no certified summary",
        SummaryBlocker::MissingReturn => "a function return could not be certified",
        SummaryBlocker::RecursiveCycle => "a recursive call could not be certified",
        SummaryBlocker::ContextBudget => "the context analysis budget was exhausted",
        SummaryBlocker::ForeignDefinition
        | SummaryBlocker::ForeignCall
        | SummaryBlocker::WrongContext
        | SummaryBlocker::WrongArity { .. } => "the analysis context could not be validated",
    }
}
