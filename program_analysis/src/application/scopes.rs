use std::collections::{BTreeMap, BTreeSet, VecDeque};

use parser::hir::DefinitionRef;
use parser::new_frontend::Span;
use program_structure::report::Report;

use crate::application::diagnostics::{Diagnostics, IncompleteCause, IncompleteDetail};
use crate::application::ApplicationError;
use crate::hir_cfg::build_cfg;
use crate::hir_facts::AnalysisFacts;
use crate::interprocedural::{
    AnalyzeEvidenceError, CallBlocker, CallOwner, CallReachability, ContextEvidence,
    ProjectSummaries, SummaryBlocker,
};
use crate::new_rules::{run_registered, RuleContext, SourceMap};

const CONTEXT_BUDGET: usize = 1024;

pub(super) struct ScopeRunner<'a, 'b, 'c, 'd> {
    summaries: &'a ProjectSummaries<'b>,
    sources: &'a SourceMap<'c>,
    diagnostics: &'d mut Diagnostics<'a, 'c>,
    pending: VecDeque<ContextEvidence>,
    seen: BTreeSet<ContextEvidence>,
    reports: BTreeMap<DefinitionRef, Vec<Report>>,
}

impl<'a, 'b, 'c, 'd> ScopeRunner<'a, 'b, 'c, 'd> {
    pub(super) fn new(
        summaries: &'a ProjectSummaries<'b>,
        sources: &'a SourceMap<'c>,
        diagnostics: &'d mut Diagnostics<'a, 'c>,
    ) -> Self {
        Self {
            summaries,
            sources,
            diagnostics,
            pending: VecDeque::new(),
            seen: BTreeSet::new(),
            reports: BTreeMap::new(),
        }
    }

    pub(super) fn analyze(&mut self) -> Result<(), ApplicationError> {
        for site in self.summaries.graph().sites() {
            let CallOwner::Main(_) = site.owner else { continue };
            match self.summaries.graph().reachable_main_call(site.id(), self.summaries.hir()) {
                CallReachability::Reachable(call) => match self.summaries.main_evidence(&call) {
                    Ok(evidence) => self.pending.push_back(evidence),
                    Err(reason) => self.source_blocked(site.span, &reason),
                },
                CallReachability::Unavailable(_) => self
                    .diagnostics
                    .source_incomplete(site.span, "the main component could not be resolved"),
                CallReachability::Unreachable => {}
            }
        }
        self.drain()?;
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
            match self.summaries.symbolic_root(definition) {
                Ok(evidence) => self.pending.push_back(evidence),
                Err(reason) => self.source_blocked(self.span(definition)?, &reason),
            }
        }
        self.drain()
    }

    fn drain(&mut self) -> Result<(), ApplicationError> {
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
            self.analyze_scope(&evidence)?;
        }
        Ok(())
    }

    fn analyze_scope(&mut self, evidence: &ContextEvidence) -> Result<(), ApplicationError> {
        let definition = evidence.context().definition();
        self.diagnostics.begin_scope(evidence, self.span(definition)?, self.body_span(definition)?);
        let cfg = build_cfg(self.summaries.hir(), definition).map_err(|error| {
            ApplicationError::Invariant(format!("invalid control flow: {error:?}"))
        })?;
        let facts = match self.summaries.analyze_for_evidence(&cfg, evidence, None) {
            Ok(facts) => facts,
            Err(error) => {
                self.analysis_error(evidence, self.span(definition)?, error)?;
                self.reports.entry(definition).or_default();
                return Ok(());
            }
        };
        let context = RuleContext::new(&facts, self.summaries, evidence).map_err(|error| {
            ApplicationError::Invariant(format!("invalid rule context: {error:?}"))
        })?;
        let result = run_registered(&context)
            .map_err(|error| ApplicationError::Invariant(error.to_string()))?;
        let reports = self.reports.entry(definition).or_default();
        for finding in result.findings() {
            let mut report = finding.to_report(self.sources)?;
            for site in evidence.call_path() {
                let (file, range) = self.sources.location(site.span())?;
                report.add_secondary(range, file, Some("Reached through this call.".to_string()));
            }
            reports.push(report);
        }
        for abstention in result.abstentions() {
            self.diagnostics.scope_incomplete(
                evidence,
                self.span(abstention.definition())?,
                IncompleteDetail {
                    span: abstention.span,
                    reason: IncompleteCause::Rule(abstention.reason.clone()),
                    rule: Some(abstention.kind),
                },
            );
        }
        self.enqueue_calls(&facts, evidence)?;
        Ok(())
    }

    fn enqueue_calls(
        &mut self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<(), ApplicationError> {
        for site in self
            .summaries
            .graph()
            .calls_from(CallOwner::Definition(evidence.context().definition()))
        {
            let child = match self.summaries.graph().reachable_call(site.id(), facts) {
                CallReachability::Unreachable => continue,
                CallReachability::Reachable(call) => {
                    self.summaries.call_evidence(&call, facts, evidence)
                }
                CallReachability::Unavailable(CallBlocker::ProvisionalSite) => {
                    self.summaries.refined_function_call_evidence(site.id(), facts, evidence)
                }
                CallReachability::Unavailable(_) => {
                    self.context_blocked(evidence, site.span, &SummaryBlocker::ExternalSummary)?;
                    continue;
                }
            };
            match child {
                Ok(child) => self.pending.push_back(child),
                Err(reason) => self.context_blocked(evidence, site.span, &reason)?,
            }
        }
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
                self.context_blocked(evidence, span, &reason)?
            }
            AnalyzeEvidenceError::InvalidAssignment { diagnostic, .. }
            | AnalyzeEvidenceError::InvalidValueUse { diagnostic, .. } => {
                self.diagnostics.push(self.sources.semantic_report(&diagnostic)?);
                self.diagnostics.scope_incomplete(
                    evidence,
                    self.span(evidence.context().definition())?,
                    IncompleteDetail {
                        span,
                        reason: IncompleteCause::Source(
                            "an assignment or value use is invalid".into(),
                        ),
                        rule: None,
                    },
                );
            }
        }
        Ok(())
    }

    fn source_blocked(&mut self, span: Span, reason: &SummaryBlocker) {
        self.diagnostics
            .source_incomplete(span, IncompleteCause::Summary(reason.clone()).message());
    }

    fn context_blocked(
        &mut self,
        evidence: &ContextEvidence,
        span: Span,
        reason: &SummaryBlocker,
    ) -> Result<(), ApplicationError> {
        self.diagnostics.scope_incomplete(
            evidence,
            self.span(evidence.context().definition())?,
            IncompleteDetail { span, reason: IncompleteCause::Summary(reason.clone()), rule: None },
        );
        Ok(())
    }

    fn body_span(&self, definition: DefinitionRef) -> Result<Span, ApplicationError> {
        let hir = self.summaries.hir();
        let span = match definition {
            DefinitionRef::Function(id) => hir.function(id).map(|item| item.span),
            DefinitionRef::Template(id) => hir.template(id).map(|item| item.span),
            DefinitionRef::Bus(id) => hir.bus(id).map(|item| item.span),
        };
        span.ok_or_else(|| ApplicationError::Invariant("missing source definition".into()))
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

    pub(super) fn finish(self) -> BTreeMap<DefinitionRef, Vec<Report>> {
        self.reports
    }
}
