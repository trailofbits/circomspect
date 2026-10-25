//! A call context checked against one immutable caller analysis.

use abstract_interpretation::graph::{FlowGraph, NodeId};
use parser::hir::{DefinitionRef, ExprId};

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::{AccessHandle, AnalysisFacts, InstanceRelation};
use crate::interprocedural::component::AppliedComponentPort;
use crate::interprocedural::component_port::LocalOutputPort;
use crate::interprocedural::output_enumeration::exact_instance_indices;
use crate::interprocedural::template::port_summary;
use crate::interprocedural::{
    ContextEvidence, PortSummary, ProjectSummaries, ReachableCall, SummaryBlocker,
};

#[derive(Clone)]
pub(in crate::interprocedural) struct CheckedCallContext<'query, 'project> {
    provider: &'query ProjectSummaries<'project>,
    facts: &'query AnalysisFacts<'query>,
    caller: &'query ContextEvidence,
    callee: ContextEvidence,
    expression: Option<ExprId>,
}

impl<'query, 'project> CheckedCallContext<'query, 'project> {
    pub(in crate::interprocedural) fn new(
        provider: &'query ProjectSummaries<'project>,
        facts: &'query AnalysisFacts<'query>,
        caller: &'query ContextEvidence,
        call: &ReachableCall<'_>,
    ) -> Result<Self, SummaryBlocker> {
        let callee = provider.call_evidence(call, facts, caller)?;
        Ok(Self { provider, facts, caller, callee, expression: call.site().expression })
    }

    pub(in crate::interprocedural) fn with_port_facts<T>(
        &self,
        work: impl FnOnce(&AnalysisFacts<'_>) -> Result<T, SummaryBlocker>,
    ) -> Result<T, SummaryBlocker> {
        self.provider.with_component_port_facts(&self.callee, work)
    }

    pub(in crate::interprocedural) fn apply_local_port(
        &self,
        local: LocalOutputPort<'_, '_>,
    ) -> Result<AppliedComponentPort, SummaryBlocker> {
        let summary = self.local_summary(local)?;
        let (component, target, _) =
            self.provider.instantiated_component(self.facts, self.expression)?;
        let bounds = self
            .facts
            .component_bounds(component)
            .map_err(|_| SummaryBlocker::UnsupportedContext)?;
        let indices = exact_instance_indices(self.facts, &target, &bounds)?;
        let handle = self
            .facts
            .component_output_from_local(component, &indices, local.handle)
            .map_err(|_| SummaryBlocker::UnsupportedContext)?;
        self.check_output(&handle, &summary)?;
        let instantiation =
            self.provider.bind_instantiation(self.facts, self.expression, &handle)?;
        Ok(self.issue_output(handle, summary, instantiation))
    }

    fn local_summary(&self, local: LocalOutputPort<'_, '_>) -> Result<PortSummary, SummaryBlocker> {
        self.provider.check_facts_for_evidence(local.facts, &self.callee)?;
        if !local.handle.matches_context(self.callee.context()) {
            return Err(SummaryBlocker::WrongContext);
        }
        let (port, indices) = self.provider.local_output_key(local.handle)?;
        port_summary(local.facts, self.callee.context(), port, &indices)
    }

    fn check_output(
        &self,
        handle: &AccessHandle,
        port: &PortSummary,
    ) -> Result<(), SummaryBlocker> {
        if !handle.matches_context(self.caller.context()) || port.context() != self.callee.context()
        {
            return Err(SummaryBlocker::WrongContext);
        }
        let (id, indices) = handle.output_port().ok_or(SummaryBlocker::WrongInstance)?;
        if id != port.port() || indices != port.indices() {
            return Err(SummaryBlocker::WrongInstance);
        }
        Ok(())
    }

    fn bind_output_at(
        &self,
        handle: AccessHandle,
        port: PortSummary,
        instantiation: NodeId,
    ) -> Result<AppliedComponentPort, SummaryBlocker> {
        self.check_output(&handle, &port)?;
        Ok(self.issue_output(handle, port, instantiation))
    }

    fn issue_output(
        &self,
        handle: AccessHandle,
        port: PortSummary,
        instantiation: NodeId,
    ) -> AppliedComponentPort {
        AppliedComponentPort {
            caller: self.caller.clone(),
            callee: self.callee.clone(),
            handle,
            port,
            instantiation,
        }
    }
}

impl ProjectSummaries<'_> {
    pub(in crate::interprocedural::component) fn component_output_result(
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
        let instantiation = self.bind_instantiation(facts, call.site().expression, handle)?;
        let context = CheckedCallContext::new(self, facts, caller, call)?;
        let (port, indices) = handle.output_port().ok_or(SummaryBlocker::WrongInstance)?;
        let summary = self.template_port_at(template, context.callee.context(), port, &indices);
        let port = summary.certified().cloned().ok_or_else(|| {
            summary
                .unavailable()
                .and_then(|blockers| blockers.iter().next())
                .cloned()
                .unwrap_or(SummaryBlocker::ExternalSummary)
        })?;
        context.bind_output_at(handle.clone(), port, instantiation)
    }

    fn bind_instantiation(
        &self,
        facts: &AnalysisFacts<'_>,
        expression: Option<ExprId>,
        handle: &AccessHandle,
    ) -> Result<NodeId, SummaryBlocker> {
        let cfg = facts.cfg();
        let mut count = 0;
        let mut matched = None;
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
            if self.direct_call_expression(*value) == expression {
                matched = Some(*id);
            }
        }
        if count > 1 {
            return Err(SummaryBlocker::DuplicateInstance);
        }
        matched.ok_or(SummaryBlocker::WrongInstance)
    }
}
