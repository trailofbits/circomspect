//! Checked binding of a local template port summary to one component instance.

use abstract_interpretation::graph::FlowGraph;
use parser::hir::{DefinitionRef, ExprId, ExprKind};

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::{AccessHandle, AnalysisFacts, InstanceRelation};

use super::{
    ContextEvidence, PortSummary, ProjectSummaries, ReachableCall, SummaryBlocker, SummaryFact,
};

/// A child-local output fact bound to one reachable, exact caller instance.
///
/// The binding does not prove that all caller-side input or output relations are closed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AppliedComponentPort {
    caller: ContextEvidence,
    callee: ContextEvidence,
    handle: AccessHandle,
    port: PortSummary,
}

impl AppliedComponentPort {
    #[must_use]
    pub fn caller_evidence(&self) -> &ContextEvidence {
        &self.caller
    }

    #[must_use]
    pub fn callee_evidence(&self) -> &ContextEvidence {
        &self.callee
    }

    #[must_use]
    pub fn handle(&self) -> &AccessHandle {
        &self.handle
    }

    #[must_use]
    pub fn port_summary(&self) -> &PortSummary {
        &self.port
    }
}

impl ProjectSummaries<'_> {
    /// Bind one child output summary to a proved caller call and exact instance.
    pub fn apply_component_output(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
        call: &ReachableCall<'_>,
        handle: &AccessHandle,
    ) -> SummaryFact<AppliedComponentPort> {
        SummaryFact::from_result(self.component_output_result(facts, caller, call, handle))
    }

    fn component_output_result(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
        call: &ReachableCall<'_>,
        handle: &AccessHandle,
    ) -> Result<AppliedComponentPort, SummaryBlocker> {
        self.check_facts_for_evidence(facts, caller)?;
        let DefinitionRef::Template(template) = call.callee() else {
            return Err(SummaryBlocker::WrongInstance);
        };
        if !handle.matches_context(caller.context()) {
            return Err(SummaryBlocker::WrongContext);
        }
        let component = handle.component().ok_or(SummaryBlocker::WrongInstance)?;
        let component = facts.hir().component(component).ok_or(SummaryBlocker::WrongInstance)?;
        if handle.path().root != component.symbol {
            return Err(SummaryBlocker::WrongInstance);
        }
        self.bind_instantiation(facts, call, handle)?;
        let callee = self.call_evidence(call, facts)?;
        let (port, indices) = handle.output_port().ok_or(SummaryBlocker::WrongInstance)?;
        let summary = self.template_port_at(template, callee.context(), port, &indices);
        let port = summary.certified().cloned().ok_or_else(|| {
            summary
                .unavailable()
                .and_then(|blockers| blockers.iter().next())
                .cloned()
                .unwrap_or(SummaryBlocker::ExternalSummary)
        })?;
        Ok(AppliedComponentPort { caller: caller.clone(), callee, handle: handle.clone(), port })
    }

    fn bind_instantiation(
        &self,
        facts: &AnalysisFacts<'_>,
        call: &ReachableCall<'_>,
        handle: &AccessHandle,
    ) -> Result<(), SummaryBlocker> {
        let cfg = facts.cfg();
        let mut count = 0;
        let mut matched = false;
        for id in cfg.nodes() {
            let Some(CfgNodeKind::Instantiate { target, value }) =
                cfg.node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            if target.root != handle.path().root {
                continue;
            }
            let relation = facts.instance_relation(handle, target);
            if relation == InstanceRelation::Separate {
                continue;
            }
            match facts.reachable_node(*id).certified() {
                Some(false) => continue,
                None => return Err(SummaryBlocker::ExternalSummary),
                Some(true) => {}
            }
            if relation == InstanceRelation::Possible {
                return Err(SummaryBlocker::SymbolicInstance);
            }
            count += 1;
            matched |= self.direct_call_expression(*value) == call.site().expression;
        }
        if count > 1 {
            return Err(SummaryBlocker::DuplicateInstance);
        }
        if !matched {
            return Err(SummaryBlocker::WrongInstance);
        }
        Ok(())
    }

    fn direct_call_expression(&self, expression: ExprId) -> Option<ExprId> {
        let expression_node = self.hir().expression(expression)?;
        match expression_node.kind {
            ExprKind::Parallel(inner) => self.direct_call_expression(inner),
            ExprKind::Call { .. } => Some(expression),
            ExprKind::Number(_)
            | ExprKind::Access(_)
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Array(_)
            | ExprKind::Tuple(_)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Ternary { .. }
            | ExprKind::Opaque(_) => None,
        }
    }
}
