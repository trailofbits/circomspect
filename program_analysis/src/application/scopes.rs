use std::collections::{BTreeMap, BTreeSet, VecDeque};
use abstract_interpretation::timeout::{Timeout, check, within};

use parser::hir::DefinitionRef;
use parser::frontend::Span;
use program_structure::report::Report;

use crate::application::coverage::{CoverageContext, CoverageExplanation};
use crate::application::diagnostics::Diagnostics;
use crate::application::grouping::{ContextDisplay, ReportGroups};
use crate::application::{AnalysisObserver, AnalysisProgress, ApplicationError};
use crate::hir_cfg::build_cfg;
use crate::hir_facts::AnalysisFacts;
use crate::interprocedural::{
    AnalyzeEvidenceError, CallBlocker, CallOwner, CallReachability, ContextEvidence,
    ProjectAnalysis, SummaryBlocker,
};
use crate::rules::{RuleKind, SourceMap, run_registered, RuleContext};

const CONTEXT_BUDGET: usize = 1024;

struct ScopeNote {
    span: Span,
    explanations: Vec<CoverageExplanation>,
}

enum CallOutcome {
    Child(ContextEvidence),
    Blocked { span: Span, reason: SummaryBlocker },
    Incomplete(ScopeNote),
}

struct ComputedScope {
    reports: Vec<(Report, ContextDisplay)>,
    notes: Vec<ScopeNote>,
    calls: Vec<CallOutcome>,
}

enum ScopeOutcome {
    Complete(ComputedScope),
    Failed(AnalyzeEvidenceError),
}

pub(super) struct ScopeRunner<'a, 'b, 'c, 'd> {
    summaries: &'a ProjectAnalysis<'b>,
    sources: &'a SourceMap<'c>,
    diagnostics: &'d mut Diagnostics<'a, 'c>,
    timeout: Timeout,
    pending: VecDeque<ContextEvidence>,
    seen: BTreeSet<ContextEvidence>,
    reports: BTreeMap<DefinitionRef, ReportGroups>,
}

impl<'a, 'b, 'c, 'd> ScopeRunner<'a, 'b, 'c, 'd> {
    pub(super) fn new(
        summaries: &'a ProjectAnalysis<'b>,
        sources: &'a SourceMap<'c>,
        diagnostics: &'d mut Diagnostics<'a, 'c>,
        timeout: Timeout,
    ) -> Self {
        Self {
            summaries,
            sources,
            diagnostics,
            timeout,
            pending: VecDeque::new(),
            seen: BTreeSet::new(),
            reports: BTreeMap::new(),
        }
    }

    pub(super) fn analyze(
        &mut self,
        observer: &mut dyn AnalysisObserver,
    ) -> Result<(), ApplicationError> {
        for site in self.summaries.graph().sites() {
            let CallOwner::Main(_) = site.owner else { continue };
            if site.expression.is_some() {
                continue;
            }
            match self.summaries.graph().reachable_main_call(site.id(), self.summaries.hir()) {
                CallReachability::Reachable(call) => {
                    match self.summaries.contexts().main_evidence(&call) {
                        Ok(evidence) => self.pending.push_back(evidence),
                        Err(reason) => self.source_blocked(site.span, &reason),
                    }
                }
                CallReachability::Unavailable(reason) => {
                    let coverage = CoverageContext {
                        hir: self.summaries.hir(),
                        facts: None,
                        evidence: None,
                        span: site.span,
                    };
                    for explanation in coverage.call(&reason) {
                        self.diagnostics.source_incomplete(explanation);
                    }
                }
                CallReachability::Unreachable => {}
            }
        }
        self.drain(observer)?;
        let mut definitions = Vec::new();
        for function in self.summaries.hir().functions() {
            definitions.push(DefinitionRef::Function(function.id));
        }
        for template in self.summaries.hir().templates() {
            definitions.push(DefinitionRef::Template(template.id));
        }
        for bus in self.summaries.hir().buses() {
            definitions.push(DefinitionRef::Bus(bus.id));
        }
        for definition in definitions {
            if self.reports.contains_key(&definition) {
                continue;
            }
            match self.summaries.contexts().symbolic_root(definition) {
                Ok(evidence) => self.pending.push_back(evidence),
                Err(reason) => self.source_blocked(self.span(definition)?, &reason),
            }
        }
        self.drain(observer)
    }

    fn drain(&mut self, observer: &mut dyn AnalysisObserver) -> Result<(), ApplicationError> {
        while let Some(evidence) = self.pending.pop_front() {
            if self.seen.contains(&evidence) {
                continue;
            }
            if self.seen.len() >= CONTEXT_BUDGET {
                self.context_blocked(
                    &evidence,
                    self.span(evidence.context().definition())?,
                    &SummaryBlocker::ContextBudget,
                )?;
                continue;
            }
            self.seen.insert(evidence.clone());
            let definition = evidence.context().definition();
            observer.progress(self.scope_progress(definition)?)?;
            match within(self.timeout, || self.compute_scope(&evidence)) {
                Ok(outcome) => self.apply_scope(&evidence, outcome?)?,
                Err(_) => self.scope_timed_out(&evidence)?,
            }
            self.diagnostics.emit_new(observer)?;
            if self.is_input_scope(definition)? {
                if let Some(reports) = self.reports.get_mut(&definition) {
                    reports.emit_new(self.sources, observer)?;
                }
            }
        }
        Ok(())
    }

    fn scope_progress(
        &self,
        definition: DefinitionRef,
    ) -> Result<AnalysisProgress<'_>, ApplicationError> {
        let hir = self.summaries.hir();
        let progress = match definition {
            DefinitionRef::Function(id) => {
                hir.function(id).map(|item| AnalysisProgress::AnalyzingFunction(&item.name))
            }
            DefinitionRef::Template(id) => {
                hir.template(id).map(|item| AnalysisProgress::AnalyzingTemplate(&item.name))
            }
            DefinitionRef::Bus(id) => {
                hir.bus(id).map(|item| AnalysisProgress::AnalyzingBus(&item.name))
            }
        };
        progress.ok_or_else(|| ApplicationError::Invariant("missing source definition".into()))
    }

    fn compute_scope(&self, evidence: &ContextEvidence) -> Result<ScopeOutcome, ApplicationError> {
        check();
        let facts = match self.summaries.contexts().analyze_without_cfg(evidence, None) {
            Ok(facts) => facts,
            Err(error) => return Ok(ScopeOutcome::Failed(error)),
        };
        check();
        let context = RuleContext::new(&facts, self.summaries, evidence).map_err(|error| {
            ApplicationError::Invariant(format!("invalid rule context: {error:?}"))
        })?;
        let result = run_registered(&context)
            .map_err(|error| ApplicationError::Invariant(error.to_string()))?;
        let needs_source_cfg = !evidence.call_path().is_empty()
            && !evidence.context().arguments().is_empty()
            && result.findings().iter().any(|finding| {
                finding.kind() == RuleKind::UnusedVariableValue
                    || finding.kind() == RuleKind::SideEffectFreeAssignment
            });
        let source_cfg = if needs_source_cfg {
            build_cfg(self.summaries.hir(), evidence.context().definition()).ok()
        } else {
            None
        };
        let mut reports = Vec::new();
        for finding in result.findings() {
            check();
            let cfg = source_cfg.as_ref().unwrap_or_else(|| facts.cfg());
            let display = ContextDisplay::for_finding(finding, cfg, self.summaries.hir(), evidence);
            reports.push((finding.to_report(self.sources)?, display));
        }
        let mut notes = Vec::new();
        for abstention in result.abstentions() {
            check();
            let coverage = CoverageContext {
                hir: self.summaries.hir(),
                facts: Some(&facts),
                evidence: Some(evidence),
                span: abstention.span,
            };
            notes.push(ScopeNote {
                span: self.span(abstention.definition())?,
                explanations: coverage.rule(&abstention.reason),
            });
        }
        let calls = self.compute_calls(&facts, evidence)?;
        Ok(ScopeOutcome::Complete(ComputedScope { reports, notes, calls }))
    }

    fn compute_calls(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<Vec<CallOutcome>, ApplicationError> {
        let mut outcomes = Vec::new();
        for site in self
            .summaries
            .graph()
            .calls_from(CallOwner::Definition(evidence.context().definition()))
        {
            check();
            let child = match self.summaries.graph().reachable_call(site.id(), facts) {
                CallReachability::Unreachable => continue,
                CallReachability::Reachable(call) => {
                    self.summaries.contexts().call_evidence(&call, facts, evidence)
                }
                CallReachability::Unavailable(CallBlocker::ProvisionalSite) => self
                    .summaries
                    .contexts()
                    .refined_function_call_evidence(site.id(), facts, evidence),
                CallReachability::Unavailable(reason) => {
                    let coverage = CoverageContext {
                        hir: self.summaries.hir(),
                        facts: Some(facts),
                        evidence: Some(evidence),
                        span: site.span,
                    };
                    outcomes.push(CallOutcome::Incomplete(ScopeNote {
                        span: self.span(evidence.context().definition())?,
                        explanations: coverage.call(&reason),
                    }));
                    continue;
                }
            };
            match child {
                Ok(child) => outcomes.push(CallOutcome::Child(child)),
                Err(reason) => outcomes.push(CallOutcome::Blocked { span: site.span, reason }),
            }
        }
        Ok(outcomes)
    }

    fn apply_scope(
        &mut self,
        evidence: &ContextEvidence,
        outcome: ScopeOutcome,
    ) -> Result<(), ApplicationError> {
        let definition = evidence.context().definition();
        let computed = match outcome {
            ScopeOutcome::Complete(computed) => computed,
            ScopeOutcome::Failed(error) => {
                self.analysis_error(evidence, self.span(definition)?, error)?;
                self.reports.entry(definition).or_default();
                return Ok(());
            }
        };
        let reports = self.reports.entry(definition).or_default();
        for (report, display) in computed.reports {
            reports.insert(report, display);
        }
        for note in computed.notes {
            self.diagnostics.scope_incomplete(evidence, note.span, note.explanations);
        }
        for call in computed.calls {
            match call {
                CallOutcome::Child(child) => self.pending.push_back(child),
                CallOutcome::Blocked { span, reason } => {
                    self.context_blocked(evidence, span, &reason)?;
                }
                CallOutcome::Incomplete(note) => {
                    self.diagnostics.scope_incomplete(evidence, note.span, note.explanations);
                }
            }
        }
        Ok(())
    }

    fn scope_timed_out(&mut self, evidence: &ContextEvidence) -> Result<(), ApplicationError> {
        let definition = evidence.context().definition();
        let Timeout::Bounded(duration) = self.timeout else { return Ok(()) };
        let hir = self.summaries.hir();
        let (name, kind) = match definition {
            DefinitionRef::Function(id) => {
                (hir.function(id).map(|item| item.name.as_str()), "function")
            }
            DefinitionRef::Template(id) => {
                (hir.template(id).map(|item| item.name.as_str()), "template")
            }
            DefinitionRef::Bus(id) => (hir.bus(id).map(|item| item.name.as_str()), "bus"),
        };
        let name =
            name.ok_or_else(|| ApplicationError::Invariant("missing source definition".into()))?;
        self.diagnostics.timed_out(name, kind, duration);
        Ok(())
    }

    fn analysis_error(
        &mut self,
        evidence: &ContextEvidence,
        span: Span,
        error: AnalyzeEvidenceError,
    ) -> Result<(), ApplicationError> {
        match error {
            AnalyzeEvidenceError::Blocked(reason) => {
                self.context_blocked(evidence, span, &reason)?;
            }
            AnalyzeEvidenceError::InvalidAssignment { diagnostic, .. }
            | AnalyzeEvidenceError::InvalidValueUse { diagnostic, .. } => {
                self.diagnostics.push(self.sources.semantic_report(&diagnostic)?);
            }
        }
        Ok(())
    }

    fn source_blocked(&mut self, span: Span, reason: &SummaryBlocker) {
        let coverage =
            CoverageContext { hir: self.summaries.hir(), facts: None, evidence: None, span };
        for explanation in coverage.summary(reason) {
            self.diagnostics.source_incomplete(explanation);
        }
    }

    fn context_blocked(
        &mut self,
        evidence: &ContextEvidence,
        span: Span,
        reason: &SummaryBlocker,
    ) -> Result<(), ApplicationError> {
        let coverage = CoverageContext {
            hir: self.summaries.hir(),
            facts: None,
            evidence: Some(evidence),
            span,
        };
        self.diagnostics.scope_incomplete(
            evidence,
            self.span(evidence.context().definition())?,
            coverage.summary(reason),
        );
        Ok(())
    }

    fn span(&self, definition: DefinitionRef) -> Result<Span, ApplicationError> {
        let hir = self.summaries.hir();
        let span = match definition {
            DefinitionRef::Function(id) => hir.function(id).map(|item| item.name_span),
            DefinitionRef::Template(id) => hir.template(id).map(|item| item.name_span),
            DefinitionRef::Bus(id) => hir.bus(id).map(|item| item.name_span),
        };
        span.ok_or_else(|| ApplicationError::Invariant("missing source definition".to_string()))
    }

    fn is_input_scope(&self, definition: DefinitionRef) -> Result<bool, ApplicationError> {
        if let DefinitionRef::Bus(_) = definition {
            return Ok(false);
        }
        Ok(self.sources.is_root(self.span(definition)?.source()))
    }

    pub(super) fn finish(
        mut self,
        observer: &mut dyn AnalysisObserver,
    ) -> Result<BTreeMap<DefinitionRef, Vec<Report>>, ApplicationError> {
        let mut reports = BTreeMap::new();
        let mut quiet = |_: AnalysisProgress<'_>| Ok(());
        for (definition, groups) in std::mem::take(&mut self.reports) {
            let observer = if self.is_input_scope(definition)? {
                &mut *observer
            } else {
                &mut quiet as &mut dyn AnalysisObserver
            };
            reports.insert(definition, groups.finish(self.sources, observer)?);
        }
        Ok(reports)
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::time::Duration;

    use abstract_interpretation::timeout::Timeout;
    use parser::frontend::{Version, VersionPolicy, load_sources};
    use parser::hir::lift_project;
    use program_structure::constants::Curve;

    use crate::application::diagnostics::Diagnostics;
    use crate::application::scopes::ScopeRunner;
    use crate::application::AnalysisProgress;
    use crate::interprocedural::ProjectAnalysis;
    use crate::rules::SourceMap;

    #[test]
    fn timed_out_context_discards_its_findings_and_later_context_runs() {
        let path = std::env::temp_dir().join(format!(
            "circomspect-scope-timeout-{}-{:?}.circom",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::write(
            &path,
            "pragma circom 2.2.3; template First(){var dead=1;} \
             template Second(){var dead=2;}",
        )
        .unwrap();
        let loaded = load_sources(
            std::slice::from_ref(&path),
            &[],
            VersionPolicy::new(Version::new(2, 2, 3)),
        );
        fs::remove_file(path).unwrap();
        let lifted = lift_project(&loaded);
        let project = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let first_definition = lifted.hir.definition("First").unwrap();
        let first = project.contexts().symbolic_root(first_definition).unwrap();
        let second =
            project.contexts().symbolic_root(lifted.hir.definition("Second").unwrap()).unwrap();
        let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
        let mut diagnostics = Diagnostics::new(&sources);
        let mut runner = ScopeRunner::new(
            &project,
            &sources,
            &mut diagnostics,
            Timeout::Bounded(Duration::ZERO),
        );
        let mut progress = Vec::new();
        let mut observer = |event: AnalysisProgress<'_>| {
            progress.push(format!("{event:?}"));
            Ok(())
        };
        runner.pending.push_back(first);
        runner.drain(&mut observer).unwrap();
        runner.timeout = Timeout::Unlimited;
        runner.pending.push_back(second);
        runner.drain(&mut observer).unwrap();
        let reports = runner.finish(&mut observer).unwrap();
        let diagnostics = diagnostics.finish(&mut observer).unwrap();
        assert_eq!(diagnostics.iter().filter(|report| report.id() == "T3002").count(), 1);
        assert!(diagnostics
            .iter()
            .filter(|report| report.id() == "T3002")
            .all(|report| { report.primary().is_empty() && report.secondary().is_empty() }));
        assert!(!reports.contains_key(&first_definition));
        assert!(reports.values().any(|scope| scope.iter().any(|report| report.id() == "CS0006")));
        assert_eq!(progress.iter().filter(|entry| entry.contains("AnalyzingTemplate")).count(), 2);
    }
}
