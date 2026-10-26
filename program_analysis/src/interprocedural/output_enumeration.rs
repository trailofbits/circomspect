//! Bounded enumeration of checked direct-child output paths in one source scope.

use abstract_interpretation::graph::{FlowGraph, NodeId};
use num_traits::ToPrimitive;
use parser::hir::{AccessPath, AccessStep, ArrayIndex, ComponentId, DefinitionRef, ExprId, PortId};
use parser::frontend::{PortDirection, Span};

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::{AnalysisFacts, Range};
use crate::interprocedural::component_port::LocalOutputPort;
use crate::interprocedural::component::binding::CheckedComponentCall;

use crate::interprocedural::{
    AppliedComponentPort, CallBlocker, CallOwner, CallReachability, CallSiteId, ContextEvidence,
    ProjectAnalysis, ReachableCall, SummaryBlocker, SummaryFact,
};

const MAX_OUTPUT_HANDLES: usize = 256;

/// One exact child output, retaining the source call that instantiated it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EnumeratedComponentOutput {
    site: CallSiteId,
    source_span: Span,
    applied: AppliedComponentPort,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct EnumeratedComponentInstance {
    pub site: CallSiteId,
    pub instantiation: NodeId,
    pub target: AccessPath,
    pub component: ComponentId,
    pub indices: Vec<usize>,
    pub callee: ContextEvidence,
    pub outputs: Vec<EnumeratedComponentOutput>,
}

impl EnumeratedComponentOutput {
    pub(super) fn new(site: CallSiteId, source_span: Span, applied: AppliedComponentPort) -> Self {
        Self { site, source_span, applied }
    }

    #[must_use]
    pub fn site(&self) -> CallSiteId {
        self.site
    }

    #[must_use]
    pub fn source_span(&self) -> Span {
        self.source_span
    }

    #[must_use]
    pub fn applied_port(&self) -> &AppliedComponentPort {
        &self.applied
    }
}

struct Enumeration {
    outputs: Vec<EnumeratedComponentOutput>,
    inspected: usize,
    limit: usize,
}

impl Enumeration {
    fn reserve(&mut self) -> Result<(), SummaryBlocker> {
        if self.inspected >= self.limit {
            return Err(SummaryBlocker::ContextBudget);
        }
        self.inspected += 1;
        Ok(())
    }
}

impl ProjectAnalysis<'_> {
    /// Enumerate all checked direct-child output paths in this exact source scope.
    ///
    /// A certificate means every reachable template call, instance index, and
    /// output port index was examined. Unknown shape, call, or the 256-handle
    /// bound returns unavailable evidence instead of a partial list.
    pub fn exact_component_outputs(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
    ) -> SummaryFact<Vec<EnumeratedComponentOutput>> {
        SummaryFact::from_result(self.enumerate_outputs(facts, caller))
    }

    fn enumerate_outputs(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
    ) -> Result<Vec<EnumeratedComponentOutput>, SummaryBlocker> {
        let mut state =
            Enumeration { outputs: Vec::new(), inspected: 0, limit: MAX_OUTPUT_HANDLES };
        self.visit_component_calls(facts, caller, |call| {
            let remaining = MAX_OUTPUT_HANDLES - state.inspected;
            let instance = self.enumerate_call(facts, caller, call, remaining)?;
            for output in instance.outputs {
                state.reserve()?;
                state.outputs.push(output);
            }
            Ok(())
        })?;
        Ok(state.outputs)
    }

    pub(super) fn visit_component_calls(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
        mut visit: impl FnMut(&ReachableCall<'_>) -> Result<(), SummaryBlocker>,
    ) -> Result<(), SummaryBlocker> {
        self.check_facts_for_evidence(facts, caller)?;
        self.validated_definition(facts)?;
        let owner = CallOwner::Definition(facts.definition());
        for site in self.graph().calls_from(owner) {
            let Some(expression) = site.expression else {
                return Err(SummaryBlocker::UnsupportedCallForm);
            };
            if facts.reachable_expression(expression).certified() == Some(&false) {
                continue;
            }
            if let Some(DefinitionRef::Function(_) | DefinitionRef::Bus(_)) = site.resolved() {
                continue;
            }
            let call = self.graph().reachable_call(site.id(), facts);
            match call {
                CallReachability::Reachable(call) => visit(&call)?,
                CallReachability::Unreachable => {}
                CallReachability::Unavailable(blocker) => return Err(call_blocker(blocker)),
            }
        }
        Ok(())
    }

    pub(super) fn enumerate_call(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
        call: &ReachableCall<'_>,
        limit: usize,
    ) -> Result<EnumeratedComponentInstance, SummaryBlocker> {
        let checked = CheckedComponentCall::for_enumeration(self, facts, caller, call)?;
        let DefinitionRef::Template(child) = call.callee() else {
            return Err(SummaryBlocker::UnsupportedCallForm);
        };
        let outputs = checked.with_port_facts(|child_facts| {
            let ports = self.output_ports(child, child_facts)?;
            let mut state = Enumeration { outputs: Vec::new(), inspected: 0, limit };
            for (port, port_bounds) in &ports {
                let remaining = state.limit - state.inspected;
                let elements = checked_indices(port_bounds, remaining)?;
                for element in elements {
                    state.reserve()?;
                    let handle = child_facts
                        .port_handle(*port, &element)
                        .map_err(|_| SummaryBlocker::UnsupportedContext)?;
                    let applied = checked.apply_local_port(LocalOutputPort {
                        facts: child_facts,
                        handle: &handle,
                    })?;
                    state.outputs.push(checked.output(applied));
                }
            }
            Ok(state.outputs)
        })?;
        Ok(checked.into_enumerated(outputs))
    }

    pub(super) fn instantiated_component(
        &self,
        facts: &AnalysisFacts<'_>,
        expression: Option<ExprId>,
    ) -> Result<(ComponentId, AccessPath, NodeId), SummaryBlocker> {
        let mut component = None;
        for id in facts.cfg().nodes() {
            let Some(CfgNodeKind::Instantiate { target, value }) =
                facts.cfg().node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            if Some(*value) != expression {
                continue;
            }
            match facts.reachable_node(*id).certified() {
                Some(false) => continue,
                None => return Err(SummaryBlocker::ExternalSummary),
                Some(true) => {}
            }
            let found = self
                .hir()
                .components()
                .iter()
                .find(|item| item.symbol == target.root)
                .ok_or(SummaryBlocker::WrongInstance)?;
            if component.replace((found.id, target.clone(), *id)).is_some() {
                return Err(SummaryBlocker::DuplicateInstance);
            }
        }
        component.ok_or(SummaryBlocker::UnsupportedCallForm)
    }

    fn output_ports(
        &self,
        child: parser::hir::TemplateId,
        facts: &AnalysisFacts<'_>,
    ) -> Result<Vec<(PortId, Vec<usize>)>, SummaryBlocker> {
        let template = self.hir().template(child).ok_or(SummaryBlocker::ForeignDefinition)?;
        let mut ports = Vec::new();
        for id in &template.ports {
            let port = self.hir().port(*id).ok_or(SummaryBlocker::ForeignDefinition)?;
            if port.direction != Some(PortDirection::Output) {
                continue;
            }
            let bounds = facts
                .checked_symbol_dimensions(port.symbol)
                .map_err(|_| SummaryBlocker::UnsupportedContext)?;
            ports.push((*id, bounds));
        }
        Ok(ports)
    }
}

pub(super) fn exact_instance_indices(
    facts: &AnalysisFacts<'_>,
    target: &AccessPath,
    bounds: &[usize],
) -> Result<Vec<usize>, SummaryBlocker> {
    if target.steps.len() != bounds.len() {
        return Err(SummaryBlocker::UnsupportedContext);
    }
    let mut indices = Vec::with_capacity(bounds.len());
    for (step, bound) in target.steps.iter().zip(bounds) {
        let index = match step {
            AccessStep::Index { index: ArrayIndex::Constant(value), .. } => {
                value.parse().map_err(|_| SummaryBlocker::UnsupportedContext)?
            }
            AccessStep::Index { index: ArrayIndex::Symbolic(expression), .. } => {
                let range = facts.range(*expression);
                let Some(Range::Exact(value)) = range.certified() else {
                    return Err(SummaryBlocker::SymbolicInstance);
                };
                value.as_bigint().to_usize().ok_or(SummaryBlocker::UnsupportedContext)?
            }
            AccessStep::Port { .. } | AccessStep::Tag { .. } => {
                return Err(SummaryBlocker::UnsupportedContext);
            }
        };
        if index >= *bound {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        indices.push(index);
    }
    Ok(indices)
}

pub(super) fn checked_indices(
    bounds: &[usize],
    remaining: usize,
) -> Result<Vec<Vec<usize>>, SummaryBlocker> {
    checked_index_count(bounds, remaining)?;
    let mut indices = vec![Vec::new()];
    for bound in bounds {
        let mut next = Vec::new();
        for prefix in indices {
            for index in 0..*bound {
                let mut element = prefix.clone();
                element.push(index);
                next.push(element);
            }
        }
        indices = next;
    }
    Ok(indices)
}

pub(super) fn checked_index_count(
    bounds: &[usize],
    remaining: usize,
) -> Result<usize, SummaryBlocker> {
    let mut count = 1_usize;
    for bound in bounds {
        count = count.checked_mul(*bound).ok_or(SummaryBlocker::ContextBudget)?;
        if count > remaining {
            return Err(SummaryBlocker::ContextBudget);
        }
    }
    if count > remaining {
        return Err(SummaryBlocker::ContextBudget);
    }
    Ok(count)
}

fn call_blocker(blocker: CallBlocker) -> SummaryBlocker {
    match blocker {
        CallBlocker::LocalFacts(blockers) => SummaryBlocker::LocalFacts(blockers),
        CallBlocker::ForeignSite
        | CallBlocker::ForeignDefinition
        | CallBlocker::UnresolvedTarget
        | CallBlocker::ProvisionalSite
        | CallBlocker::MissingExpression => SummaryBlocker::ExternalSummary,
    }
}

#[cfg(test)]
mod tests {
    use crate::interprocedural::output_enumeration::{checked_index_count, checked_indices};
    use crate::interprocedural::SummaryBlocker;

    #[test]
    fn scalar_cells_obey_the_same_enumeration_budget_as_array_cells() {
        assert_eq!(checked_index_count(&[], 0), Err(SummaryBlocker::ContextBudget));
        assert_eq!(checked_indices(&[], 0), Err(SummaryBlocker::ContextBudget));
        assert_eq!(checked_index_count(&[], 1), Ok(1));
        assert_eq!(checked_indices(&[], 1), Ok(vec![Vec::<usize>::new()]));
        assert_eq!(checked_index_count(&[0], 0), Ok(0));
        assert_eq!(checked_index_count(&[512], 512), Ok(512));
        assert_eq!(checked_index_count(&[513], 512), Err(SummaryBlocker::ContextBudget));
    }
}
