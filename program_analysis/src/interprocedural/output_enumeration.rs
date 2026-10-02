//! Bounded enumeration of checked direct-child output paths in one source scope.

use abstract_interpretation::graph::FlowGraph;
use num_traits::ToPrimitive;
use parser::hir::{AccessPath, AccessStep, ArrayIndex, ComponentId, DefinitionRef, PortId};
use parser::new_frontend::{PortDirection, Span};

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::{AccessHandle, AnalysisFacts, Range};

use crate::interprocedural::{
    AppliedComponentPort, CallBlocker, CallOwner, CallReachability, CallSiteId, ContextEvidence,
    ProjectSummaries, ReachableCall, SummaryBlocker, SummaryFact,
};

const MAX_OUTPUT_HANDLES: usize = 256;

/// One exact child output, retaining the source call that instantiated it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EnumeratedComponentOutput {
    site: CallSiteId,
    source_span: Span,
    applied: AppliedComponentPort,
}

impl EnumeratedComponentOutput {
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
}

impl Enumeration {
    fn reserve(&mut self) -> Result<(), SummaryBlocker> {
        if self.inspected >= MAX_OUTPUT_HANDLES {
            return Err(SummaryBlocker::ContextBudget);
        }
        self.inspected += 1;
        Ok(())
    }
}

impl ProjectSummaries<'_> {
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
        self.check_facts_for_evidence(facts, caller)?;
        self.validated_definition(facts.definition())?;
        let owner = CallOwner::Definition(facts.definition());
        let mut state = Enumeration { outputs: Vec::new(), inspected: 0 };
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
                CallReachability::Reachable(call) => {
                    self.enumerate_call(facts, caller, &call, &mut state)?;
                }
                CallReachability::Unreachable => {}
                CallReachability::Unavailable(blocker) => return Err(call_blocker(blocker)),
            }
        }
        Ok(state.outputs)
    }

    fn enumerate_call(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
        call: &ReachableCall<'_>,
        state: &mut Enumeration,
    ) -> Result<(), SummaryBlocker> {
        let DefinitionRef::Template(child) = call.callee() else {
            return Err(SummaryBlocker::UnsupportedCallForm);
        };
        let (component, target) = self.instantiated_component(facts, call)?;
        let bounds =
            facts.component_bounds(component).map_err(|_| SummaryBlocker::UnsupportedContext)?;
        let instance = exact_instance_indices(facts, &target, &bounds)?;
        let callee = self.call_evidence(call, facts, caller)?;
        let ports = self.output_ports(child, callee.context())?;
        for (port, port_bounds) in &ports {
            let remaining = MAX_OUTPUT_HANDLES - state.inspected;
            let elements = checked_indices(port_bounds, remaining)?;
            for element in elements {
                state.reserve()?;
                let handle = facts
                    .component_output_handle(component, &instance, *port, &element)
                    .map_err(|_| SummaryBlocker::UnsupportedContext)?;
                self.push_applied(facts, caller, call, handle, state)?;
            }
        }
        Ok(())
    }

    fn instantiated_component(
        &self,
        facts: &AnalysisFacts<'_>,
        call: &ReachableCall<'_>,
    ) -> Result<(ComponentId, AccessPath), SummaryBlocker> {
        let mut component = None;
        for id in facts.cfg().nodes() {
            let Some(CfgNodeKind::Instantiate { target, value }) =
                facts.cfg().node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            if Some(*value) != call.site().expression {
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
            if component.replace((found.id, target.clone())).is_some() {
                return Err(SummaryBlocker::DuplicateInstance);
            }
        }
        component.ok_or(SummaryBlocker::UnsupportedCallForm)
    }

    fn output_ports(
        &self,
        child: parser::hir::TemplateId,
        context: &crate::interprocedural::CallContext,
    ) -> Result<Vec<(PortId, Vec<usize>)>, SummaryBlocker> {
        self.with_local_template(child, context, |template, _, facts| {
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
        })
    }

    fn push_applied(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
        call: &ReachableCall<'_>,
        handle: AccessHandle,
        state: &mut Enumeration,
    ) -> Result<(), SummaryBlocker> {
        let fact = self.apply_component_output(facts, caller, call, &handle);
        if let Some(applied) = fact.certified() {
            state.outputs.push(EnumeratedComponentOutput {
                site: call.site().id(),
                source_span: call.site().span,
                applied: applied.clone(),
            });
            return Ok(());
        }
        let blockers = fact.unavailable().ok_or(SummaryBlocker::ExternalSummary)?;
        Err(blockers.iter().next().cloned().unwrap_or(SummaryBlocker::ExternalSummary))
    }
}

fn exact_instance_indices(
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

fn checked_indices(bounds: &[usize], remaining: usize) -> Result<Vec<Vec<usize>>, SummaryBlocker> {
    let mut count = 1_usize;
    for bound in bounds {
        count = count.checked_mul(*bound).ok_or(SummaryBlocker::ContextBudget)?;
        if count > remaining {
            return Err(SummaryBlocker::ContextBudget);
        }
    }
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
