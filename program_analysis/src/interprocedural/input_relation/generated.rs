//! Generated input equations and a schema checked in both call contexts.

use std::collections::BTreeMap;
use abstract_interpretation::graph::FlowGraph;

use parser::hir::{AccessPath, AccessStep, ArrayIndex, DefinitionRef, PortSchema};
use parser::frontend::PortDirection;

use crate::hir_facts::{AccessKey, AnalysisFacts, GeneratedInputEquation, ProofBudget};
use crate::interprocedural::component::binding::CheckedCallContext;
use crate::interprocedural::input_relation::{
    solve_inputs, BindingPolicy, CheckedInputBinding, InputPortElement, RelationAnalysis,
};
use crate::interprocedural::output_enumeration::{
    checked_index_count, checked_indices, EnumeratedComponentInstance,
};
use crate::interprocedural::summary::certified;
use crate::interprocedural::{
    CallReachability, ContextEvidence, ProjectAnalysis, SummaryBlocker, ValidatedComponentPorts,
};

pub(in crate::interprocedural) struct PortAlias {
    pub(in crate::interprocedural) caller: AccessKey,
    pub(in crate::interprocedural) callee: AccessKey,
}

/// Port identities issued only after source call and both parameter contexts match.
///
/// The generated-input issuer checks complete input shape and parent/child port mapping.
/// Its evidence remains bound to actual source targets, elements, and context identities;
/// consuming the schema rechecks it against the supplied caller, child, and instance.
pub(in crate::interprocedural) struct CheckedInputSchema {
    caller: ContextEvidence,
    instance: EnumeratedComponentInstance,
    elements: BTreeMap<InputPortElement, PortAlias>,
}

impl CheckedInputSchema {
    pub(in crate::interprocedural) fn into_elements(
        self,
        facts: &AnalysisFacts<'_>,
        child: &AnalysisFacts<'_>,
        instance: &EnumeratedComponentInstance,
    ) -> Result<BTreeMap<InputPortElement, PortAlias>, SummaryBlocker> {
        if self.instance != *instance
            || !facts.matches_evidence(&self.caller)
            || !child.matches_evidence(&instance.callee)
        {
            return Err(SummaryBlocker::WrongContext);
        }
        Ok(self.elements)
    }
}

/// Complete generated bindings; their equations retain constraint provenance.
///
/// The generated-input issuer retains checked equality provenance, port mapping, and input
/// readiness for the exact parent/child contexts. Consumers still validate model keys and all
/// participating equations; witness-only bindings cannot substitute for these equalities.
pub(in crate::interprocedural) struct ReadyGeneratedInputs {
    caller: ContextEvidence,
    instance: EnumeratedComponentInstance,
    bindings: BTreeMap<InputPortElement, CheckedInputBinding<GeneratedInputEquation>>,
    ports: ValidatedComponentPorts,
}

impl ReadyGeneratedInputs {
    pub(in crate::interprocedural) fn caller(&self) -> &ContextEvidence {
        &self.caller
    }

    pub(in crate::interprocedural) fn bindings(
        &self,
    ) -> &BTreeMap<InputPortElement, CheckedInputBinding<GeneratedInputEquation>> {
        &self.bindings
    }

    pub(in crate::interprocedural) fn ports(&self) -> &ValidatedComponentPorts {
        &self.ports
    }

    pub(in crate::interprocedural) fn matches(
        &self,
        facts: &AnalysisFacts<'_>,
        instance: &EnumeratedComponentInstance,
    ) -> bool {
        self.instance == *instance
            && facts.matches_evidence(&self.caller)
            && facts.reachable_node(facts.cfg().exit()).certified() == Some(&true)
    }
}

impl ProjectAnalysis<'_> {
    pub(in crate::interprocedural) fn ready_generated_instance(
        &self,
        facts: &AnalysisFacts<'_>,
        child: &AnalysisFacts<'_>,
        instance: &EnumeratedComponentInstance,
        budget: &mut ProofBudget,
    ) -> Result<ReadyGeneratedInputs, SummaryBlocker> {
        let schema = self.generated_input_schema(facts, child, instance, budget)?;
        let caller = schema.caller.clone();
        let ports = ValidatedComponentPorts::from_schema(facts, child, instance, schema)?;
        for _ in facts.cfg().nodes() {
            if !budget.reserve_control_step() {
                return Err(SummaryBlocker::ContextBudget);
            }
        }
        let exact = exact_path(instance);
        let analysis = RelationAnalysis {
            facts,
            instance: &exact,
            instantiation: instance.instantiation,
            inputs: ports.input_elements().cloned().collect(),
            policy: BindingPolicy::GeneratedExpressions(&ports),
        };
        let bindings = solve_inputs(&analysis)?.into_bindings()?;
        Ok(ReadyGeneratedInputs { caller, instance: instance.clone(), bindings, ports })
    }

    fn generated_input_context(
        &self,
        facts: &AnalysisFacts<'_>,
        child: &AnalysisFacts<'_>,
        instance: &EnumeratedComponentInstance,
    ) -> Result<ContextEvidence, SummaryBlocker> {
        let first = instance.outputs.first().ok_or(SummaryBlocker::UnsupportedContext)?;
        let caller = first.applied_port().caller_evidence();
        self.contexts().check_facts_for_evidence(facts, caller)?;
        self.contexts().check_facts_for_evidence(child, &instance.callee)?;
        if certified(&facts.reachable_node(facts.cfg().exit()))? != &true {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        let CallReachability::Reachable(call) = self.graph().reachable_call(instance.site, facts)
        else {
            return Err(SummaryBlocker::ForeignCall);
        };
        let context = CheckedCallContext::new(self, facts, caller, &call)?;
        if context.callee() != &instance.callee {
            return Err(SummaryBlocker::WrongContext);
        }
        let checked = context.select_instance(|component, target, site| {
            if component != instance.component
                || target != &instance.target
                || site != instance.instantiation
            {
                return Err(SummaryBlocker::WrongInstance);
            }
            Ok(())
        })?;
        if checked.indices() != instance.indices {
            return Err(SummaryBlocker::WrongInstance);
        }
        for output in &instance.outputs {
            let applied = output.applied_port();
            if applied.caller_evidence() != caller
                || applied.callee_evidence() != &instance.callee
                || applied.instantiation() != checked.instantiation()
            {
                return Err(SummaryBlocker::WrongContext);
            }
        }
        Ok(caller.clone())
    }

    fn generated_input_schema(
        &self,
        facts: &AnalysisFacts<'_>,
        child: &AnalysisFacts<'_>,
        instance: &EnumeratedComponentInstance,
        budget: &mut ProofBudget,
    ) -> Result<CheckedInputSchema, SummaryBlocker> {
        let caller = self.generated_input_context(facts, child, instance)?;
        let DefinitionRef::Template(id) = child.definition() else {
            return Err(SummaryBlocker::WrongInstance);
        };
        let template = self.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
        let mut inputs = BTreeMap::new();
        for id in &template.ports {
            if !budget.reserve_control_step() {
                return Err(SummaryBlocker::ContextBudget);
            }
            let port = self.hir().port(*id).ok_or(SummaryBlocker::ForeignDefinition)?;
            if port.direction != Some(PortDirection::Input) {
                continue;
            }
            if port.schema != PortSchema::Signal {
                return Err(SummaryBlocker::UnsupportedContext);
            }
            let bounds = child
                .checked_symbol_dimensions(port.symbol)
                .map_err(|_| SummaryBlocker::UnsupportedContext)?;
            let count = checked_index_count(&bounds, 512 - inputs.len())?;
            for _ in 0..count {
                if !budget.reserve_key() || !budget.reserve_control_step() {
                    return Err(SummaryBlocker::ContextBudget);
                }
            }
            for indices in checked_indices(&bounds, count)? {
                let local = child
                    .port_handle(*id, &indices)
                    .map_err(|_| SummaryBlocker::UnsupportedContext)?;
                let parent = facts
                    .component_input_from_local(instance.component, &instance.indices, &local)
                    .map_err(|_| SummaryBlocker::UnsupportedContext)?;
                let keys = PortAlias {
                    caller: certified(&facts.component_handle_key(&parent))?.clone(),
                    callee: certified(&child.exact_handle_key(&local))?.clone(),
                };
                inputs.insert(InputPortElement { port: *id, indices }, keys);
            }
        }
        Ok(CheckedInputSchema { caller, instance: instance.clone(), elements: inputs })
    }
}

fn exact_path(instance: &EnumeratedComponentInstance) -> AccessPath {
    let steps = instance
        .indices
        .iter()
        .map(|index| AccessStep::Index {
            index: ArrayIndex::Constant(index.to_string()),
            span: instance.target.span,
        })
        .collect();
    AccessPath { steps, ..instance.target.clone() }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod context_tests;
