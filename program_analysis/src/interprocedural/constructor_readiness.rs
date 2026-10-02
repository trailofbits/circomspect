//! Provider-owned leaf constructor coverage for local signal-read validation.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use parser::hir::{DefinitionRef, ExprId};
use parser::new_frontend::PortDirection;

use crate::hir_cfg::{build_cfg, CfgNodeKind};
use crate::hir_facts::{AnalysisFacts, BodyWriteStatus};
use crate::interprocedural::{
    CallOwner, CallReachability, ContextEvidence, ProjectSummaries, SummaryBlocker,
};
use crate::interprocedural::summary::certified;

/// Constructors whose exact leaf children passed source, read, and generated-form checks.
/// This is local readiness coverage, not a successful-termination certificate.
pub(crate) struct ValidatedConstructorReads {
    evidence: ContextEvidence,
    calls: BTreeSet<ExprId>,
}

impl ValidatedConstructorReads {
    pub(crate) fn evidence(&self) -> &ContextEvidence {
        &self.evidence
    }

    pub(crate) fn contains(&self, expression: ExprId) -> bool {
        self.calls.contains(&expression)
    }
}

impl ProjectSummaries<'_> {
    pub(super) fn check_template_incidence_scope(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.check_template_constraint_scope(facts, evidence)?;
        let constructors = self.validated_constructor_reads(facts, evidence)?;
        certified(&facts.body_signal_reads_ready_with(&constructors))?;
        certified(&facts.generated_constraints_valid())?;
        Ok(())
    }

    fn validated_constructor_reads(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<ValidatedConstructorReads, SummaryBlocker> {
        const MAX_CONSTRUCTORS: usize = 64;
        let mut calls = BTreeSet::new();
        for site in self.graph().calls_from(CallOwner::Definition(facts.definition())) {
            let Some(DefinitionRef::Template(_)) = site.resolved() else { continue };
            let call = match self.graph().reachable_call(site.id(), facts) {
                CallReachability::Reachable(call) => call,
                CallReachability::Unreachable => continue,
                CallReachability::Unavailable(_) => return Err(SummaryBlocker::UnsupportedContext),
            };
            if calls.len() >= MAX_CONSTRUCTORS {
                return Err(SummaryBlocker::ContextBudget);
            }
            let child = self.call_evidence(&call, facts, evidence)?;
            self.check_leaf_constructor(&child)?;
            calls.insert(site.expression.ok_or(SummaryBlocker::ForeignCall)?);
        }
        Ok(ValidatedConstructorReads { evidence: evidence.clone(), calls })
    }

    fn check_leaf_constructor(&self, evidence: &ContextEvidence) -> Result<(), SummaryBlocker> {
        let DefinitionRef::Template(id) = evidence.context().definition() else {
            return Err(SummaryBlocker::WrongContext);
        };
        let template = self.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
        for port in &template.ports {
            let port = self.hir().port(*port).ok_or(SummaryBlocker::ForeignDefinition)?;
            if port.direction == Some(PortDirection::Input) {
                return Err(SummaryBlocker::MissingInputBinding);
            }
        }
        let cfg = build_cfg(self.hir(), evidence.context().definition()).map_err(|error| {
            SummaryBlocker::LocalAnalysis(format!("leaf constructor analysis: {error:?}"))
        })?;
        let facts = self.analyze_for_evidence(&cfg, evidence, None).map_err(|error| {
            SummaryBlocker::LocalAnalysis(format!("leaf constructor analysis: {error:?}"))
        })?;
        self.check_warning_execution_scope(&facts, evidence)?;
        self.validated_definition(&facts)?;
        if certified(&facts.reachable_node(facts.cfg().exit()))? != &true {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        certified(&facts.body_signal_reads_ready())?;
        certified(&facts.generated_constraints_valid())?;
        no_repeated_leaf_writes(&facts)
    }
}

fn no_repeated_leaf_writes(facts: &AnalysisFacts<'_>) -> Result<(), SummaryBlocker> {
    for id in facts.cfg().nodes() {
        if facts.reachable_node(*id).certified() == Some(&false) {
            continue;
        }
        let Some(node) = facts.cfg().node(*id) else {
            return Err(SummaryBlocker::UnsupportedContext);
        };
        let CfgNodeKind::Witness { target, .. } = &node.kind else { continue };
        match certified(&facts.body_write_status(target))? {
            BodyWriteStatus::NoRepeat(_) => {}
            BodyWriteStatus::DefinitelyRepeated(_) => {
                return Err(SummaryBlocker::UnsupportedContext)
            }
        }
    }
    Ok(())
}
