//! Checked aliases for output accesses actually evaluated by the parent source.

use std::collections::BTreeSet;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use parser::hir::{AccessPath, ExprKind, PortId};

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::{AnalysisFacts, InstanceRelation, ProofBudget};
use crate::interprocedural::component_port::LocalOutputPort;
use crate::interprocedural::output_enumeration::{
    exact_instance_indices, EnumeratedComponentInstance, EnumeratedComponentOutput,
};
use crate::interprocedural::summary::certified;
use crate::interprocedural::{
    AppliedComponentPort, CallReachability, ProjectSummaries, ReachableCall, SummaryBlocker,
};

impl ProjectSummaries<'_> {
    pub(in crate::interprocedural) fn single_model_call<'a>(
        &'a self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
    ) -> Result<ReachableCall<'a>, SummaryBlocker> {
        let mut found = None;
        self.visit_component_calls(facts, applied.caller_evidence(), |call| {
            if found.replace(call.site().id()).is_some() {
                return Err(SummaryBlocker::UnsupportedContext);
            }
            Ok(())
        })?;
        let site = found.ok_or(SummaryBlocker::WrongInstance)?;
        let CallReachability::Reachable(call) = self.graph().reachable_call(site, facts) else {
            return Err(SummaryBlocker::ForeignCall);
        };
        if self.call_evidence(&call, facts, applied.caller_evidence())?
            != *applied.callee_evidence()
        {
            return Err(SummaryBlocker::WrongContext);
        }
        Ok(call)
    }

    pub(in crate::interprocedural) fn model_source_instance(
        &self,
        facts: &AnalysisFacts<'_>,
        child: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
        budget: &mut ProofBudget,
    ) -> Result<EnumeratedComponentInstance, SummaryBlocker> {
        let call = self.single_model_call(facts, applied)?;
        let (component, target, instantiation) =
            self.instantiated_component(facts, call.site().expression)?;
        if instantiation != applied.instantiation()
            || facts.instance_relation(applied.handle(), &target) != InstanceRelation::Exact
        {
            return Err(SummaryBlocker::WrongInstance);
        }
        let bounds =
            facts.component_bounds(component).map_err(|_| SummaryBlocker::UnsupportedContext)?;
        let indices = exact_instance_indices(facts, &target, &bounds)?;
        let keys = self.observed_model_outputs(facts, applied, budget)?;
        let mut outputs = Vec::new();
        for (port, indices) in keys {
            let local = child
                .port_handle(port, &indices)
                .map_err(|_| SummaryBlocker::UnsupportedContext)?;
            let output = self.apply_local_port(
                facts,
                applied.caller_evidence(),
                &call,
                LocalOutputPort { facts: child, handle: &local },
            )?;
            outputs.push(EnumeratedComponentOutput::from_call(&call, output));
        }
        if !outputs.iter().any(|output| output.applied_port() == applied) {
            return Err(SummaryBlocker::WrongInstance);
        }
        Ok(EnumeratedComponentInstance {
            site: call.site().id(),
            instantiation,
            target,
            component,
            indices,
            callee: applied.callee_evidence().clone(),
            outputs,
        })
    }
    fn observed_model_outputs(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
        budget: &mut ProofBudget,
    ) -> Result<BTreeSet<(PortId, Vec<usize>)>, SummaryBlocker> {
        let mut keys = BTreeSet::from([applied
            .handle()
            .output_port()
            .ok_or(SummaryBlocker::WrongInstance)?]);
        for id in facts.cfg().nodes() {
            if !budget.reserve_control_step() {
                return Err(SummaryBlocker::ContextBudget);
            }
            let Some(path) = self.live_model_output(facts, applied, *id)? else { continue };
            let key = facts
                .source_component_port_indices(path)
                .map_err(|_| SummaryBlocker::UnsupportedContext)?;
            if !keys.contains(&key) && keys.len() >= 512 {
                return Err(SummaryBlocker::ContextBudget);
            }
            keys.insert(key);
        }
        Ok(keys)
    }

    fn live_model_output<'a>(
        &'a self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
        site: NodeId,
    ) -> Result<Option<&'a AccessPath>, SummaryBlocker> {
        let Some(CfgNodeKind::Evaluate(expression)) = facts.cfg().node(site).map(|node| &node.kind)
        else {
            return Ok(None);
        };
        let Some(ExprKind::Access(path)) =
            self.hir().expression(*expression).map(|expr| &expr.kind)
        else {
            return Ok(None);
        };
        if !path.component_output || !*certified(&facts.reachable_node(site))? {
            return Ok(None);
        }
        if facts.instance_relation(applied.handle(), path) != InstanceRelation::Exact {
            return Err(SummaryBlocker::WrongInstance);
        }
        Ok(Some(path))
    }
}
