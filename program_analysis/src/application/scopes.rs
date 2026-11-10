use std::collections::{BTreeMap, BTreeSet, VecDeque};

use parser::hir::DefinitionRef;
use parser::frontend::Span;
use program_structure::report::Report;

use crate::application::coverage::CoverageContext;
use crate::application::diagnostics::Diagnostics;
use crate::application::grouping::ReportGroups;
use crate::application::{AnalysisProgress, ApplicationError};
use crate::hir_cfg::build_cfg;
use crate::hir_facts::AnalysisFacts;
use crate::interprocedural::{
    AnalyzeEvidenceError, CallBlocker, CallOwner, CallReachability, ContextEvidence,
    ProjectAnalysis, SummaryBlocker,
};
use crate::rules::{run_registered, RuleContext, SourceMap};

const CONTEXT_BUDGET: usize = 1024;

pub(super) struct ScopeRunner<'a, 'b, 'c, 'd> {
    summaries: &'a ProjectAnalysis<'b>,
    sources: &'a SourceMap<'c>,
    diagnostics: &'d mut Diagnostics<'a, 'c>,
    pending: VecDeque<ContextEvidence>,
    seen: BTreeSet<ContextEvidence>,
    reports: BTreeMap<DefinitionRef, ReportGroups>,
}

impl<'a, 'b, 'c, 'd> ScopeRunner<'a, 'b, 'c, 'd> {
    pub(super) fn new(
        summaries: &'a ProjectAnalysis<'b>,
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

    pub(super) fn analyze(
        &mut self,
        progress: &mut dyn FnMut(AnalysisProgress<'_>) -> std::io::Result<()>,
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
        self.drain(progress)?;
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
        self.drain(progress)
    }

    fn drain(
        &mut self,
        progress: &mut dyn FnMut(AnalysisProgress<'_>) -> std::io::Result<()>,
    ) -> Result<(), ApplicationError> {
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
            progress(self.scope_progress(definition)?)?;
            self.analyze_scope(&evidence)?;
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

    fn analyze_scope(&mut self, evidence: &ContextEvidence) -> Result<(), ApplicationError> {
        let definition = evidence.context().definition();
        let cfg = build_cfg(self.summaries.hir(), definition).map_err(|error| {
            ApplicationError::Invariant(format!("invalid control flow: {error:?}"))
        })?;
        let facts = match self.summaries.contexts().analyze_for_evidence(&cfg, evidence, None) {
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
            reports.insert(finding.to_report(self.sources)?, evidence);
        }
        for abstention in result.abstentions() {
            let coverage = CoverageContext {
                hir: self.summaries.hir(),
                facts: Some(&facts),
                evidence: Some(evidence),
                span: abstention.span,
            };
            self.diagnostics.scope_incomplete(
                evidence,
                self.span(abstention.definition())?,
                coverage.rule(&abstention.reason),
                Some(abstention.kind),
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
                    self.diagnostics.scope_incomplete(
                        evidence,
                        self.span(evidence.context().definition())?,
                        coverage.call(&reason),
                        None,
                    );
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
            None,
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

    pub(super) fn finish(self) -> Result<BTreeMap<DefinitionRef, Vec<Report>>, ApplicationError> {
        let mut reports = BTreeMap::new();
        for (definition, groups) in self.reports {
            reports.insert(definition, groups.finish(self.sources)?);
        }
        Ok(reports)
    }
}
