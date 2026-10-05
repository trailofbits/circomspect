//! Candidate assembly over checked aliases; equation arithmetic stays in shared facts.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::NodeId;
use num_bigint::BigUint;

use crate::hir_facts::{
    generated_models_satisfy, generated_seeds, AccessKey, AnalysisFacts, BitDecomposition,
    BitRepresentation, FieldContext, FieldValue, GeneratedAssignments, GeneratedEquationSites,
    NoBitAmbiguityCertificate, ProofBudget,
};
use crate::interprocedural::component_models::{
    ComponentBitAmbiguity, ComponentBitAmbiguityOutcome, ComponentModelAssignment,
    ValidatedComponentPorts,
};
use crate::interprocedural::input_relation::{GeneratedInputValue, ReadyInstanceAtUse};
use crate::interprocedural::{AppliedComponentPort, SummaryBlocker};

pub(super) struct ClosureEquations<'a> {
    pub caller: &'a GeneratedEquationSites<'a>,
    pub completion: &'a GeneratedAssignments<'a>,
    pub callee: &'a GeneratedEquationSites<'a>,
    pub ports: &'a ValidatedComponentPorts,
    pub ready: &'a ReadyInstanceAtUse,
    pub relation: &'a BitDecomposition,
}

impl ClosureEquations<'_> {
    pub(super) fn check(
        &self,
        caller: &AnalysisFacts<'_>,
        child: &AnalysisFacts<'_>,
        caller_path: &BTreeSet<NodeId>,
        child_path: &BTreeSet<NodeId>,
    ) -> Result<(), SummaryBlocker> {
        if self.caller.evidence() != self.ports.evidence()
            || self.callee.evidence() != self.relation.context()
        {
            return Err(SummaryBlocker::WrongContext);
        }
        child.check_requested_model_keys(self.relation).map_err(SummaryBlocker::LocalFacts)?;
        child.check_model_keys(self.callee.keys()).map_err(SummaryBlocker::LocalFacts)?;
        let mut local = BTreeSet::new();
        for key in self.caller.keys() {
            let bound_input = self.ready.bindings().values().any(|binding| &binding.target == key);
            if self.ports.child_key(key).is_none() && !bound_input {
                local.insert(key.clone());
            }
        }
        caller.check_model_keys(&local).map_err(SummaryBlocker::LocalFacts)?;
        for (sites, path) in [(self.caller, caller_path), (self.callee, child_path)] {
            if sites.sites().iter().any(|site| !path.contains(&site.site())) {
                return Err(SummaryBlocker::UnsupportedContext);
            }
        }
        Ok(())
    }

    fn child_support(
        &self,
        budget: &mut ProofBudget,
    ) -> Result<BTreeSet<AccessKey>, SummaryBlocker> {
        let mut keys = self.callee.keys().clone();
        for key in self.caller.keys().iter().filter_map(|key| self.ports.child_key(key)) {
            add_support(&mut keys, key, budget)?;
        }
        for port in self.ready.bindings().keys() {
            let key = self.ports.input_key(port).ok_or(SummaryBlocker::WrongInstance)?;
            add_support(&mut keys, key, budget)?;
        }
        Ok(keys)
    }
}

fn add_support(
    support: &mut BTreeSet<AccessKey>,
    key: &AccessKey,
    budget: &mut ProofBudget,
) -> Result<(), SummaryBlocker> {
    if !support.contains(key) {
        if !budget.reserve_key() {
            return Err(SummaryBlocker::ContextBudget);
        }
        support.insert(key.clone());
    }
    Ok(())
}

pub(super) fn prove_closure_models(
    field: &FieldContext,
    applied: &AppliedComponentPort,
    equations: &ClosureEquations<'_>,
    budget: &mut ProofBudget,
) -> Result<ComponentBitAmbiguityOutcome, SummaryBlocker> {
    let modulus = field.modulus().to_biguint().ok_or(SummaryBlocker::UnsupportedContext)?;
    let width = equations.relation.bits().len();
    if BigUint::from(1_u8) << width <= modulus {
        return Ok(no_certificate(NoBitAmbiguityCertificate::WidthBelowFieldModulus));
    }
    let Some(baseline) = closure_baseline(field, equations, budget)? else {
        return Ok(no_certificate(NoBitAmbiguityCertificate::CandidatesRejected));
    };
    let input = baseline
        .callee
        .get(equations.relation.input())
        .ok_or(SummaryBlocker::MissingInputBinding)?
        .clone();
    let integer = input.as_bigint().to_biguint().ok_or(SummaryBlocker::UnsupportedContext)?;
    let Some(second) = BitRepresentation::new(&integer + modulus, width) else {
        return Ok(no_certificate(NoBitAmbiguityCertificate::CandidatesRejected));
    };
    let Some(first) = BitRepresentation::new(integer, width) else {
        return Ok(no_certificate(NoBitAmbiguityCertificate::CandidatesRejected));
    };
    let representations = [first, second];
    let mut assignments = [baseline.clone(), baseline];
    for (assignment, representation) in assignments.iter_mut().zip(&representations) {
        set_representation(field, equations, assignment, representation)?;
        if !equations
            .completion
            .complete(field, &mut assignment.caller, budget)
            .map_err(SummaryBlocker::LocalFacts)?
        {
            return Ok(no_certificate(NoBitAmbiguityCertificate::CandidatesRejected));
        }
    }
    if !validate_closure(field, equations, &assignments, budget)? {
        return Ok(no_certificate(NoBitAmbiguityCertificate::CandidatesRejected));
    }
    Ok(ComponentBitAmbiguityOutcome::Proved(Box::new(ComponentBitAmbiguity {
        applied: applied.clone(),
        decomposition: equations.relation.clone(),
        input,
        representations,
        assignments,
        caller_origins: equations.caller.sites().iter().map(|site| site.origin()).collect(),
        callee_origins: equations.callee.sites().iter().map(|site| site.origin()).collect(),
        binding_origins: equations
            .ready
            .bindings()
            .values()
            .flat_map(|binding| binding.origins.iter().copied())
            .collect(),
    })))
}

fn closure_baseline(
    field: &FieldContext,
    equations: &ClosureEquations<'_>,
    budget: &mut ProofBudget,
) -> Result<Option<ComponentModelAssignment>, SummaryBlocker> {
    let Some(mut parent_seeds) =
        generated_seeds(field, equations.caller, budget).map_err(SummaryBlocker::LocalFacts)?
    else {
        return Ok(None);
    };
    let Some(child_seeds) =
        generated_seeds(field, equations.callee, budget).map_err(SummaryBlocker::LocalFacts)?
    else {
        return Ok(None);
    };
    for (port, binding) in equations.ready.bindings() {
        let key = equations.ports.input_key(port).ok_or(SummaryBlocker::WrongInstance)?;
        if let GeneratedInputValue::ParentSignal(parent) = &binding.value {
            if let Some(value) = child_seeds.get(key) {
                parent_seeds.entry(parent.clone()).or_insert_with(|| value.clone());
            }
        }
    }
    let child_keys = equations.child_support(budget)?;
    let mut model = ComponentModelAssignment {
        caller: seeded_model(field, equations.caller.keys(), &parent_seeds),
        callee: seeded_model(field, &child_keys, &child_seeds),
    };
    if !equations
        .completion
        .complete(field, &mut model.caller, budget)
        .map_err(SummaryBlocker::LocalFacts)?
    {
        return Ok(None);
    }
    for (port, binding) in equations.ready.bindings() {
        let key = equations.ports.input_key(port).ok_or(SummaryBlocker::WrongInstance)?;
        let value = match &binding.value {
            GeneratedInputValue::Constant(value) => value.clone(),
            GeneratedInputValue::ParentSignal(parent) => {
                model.caller.get(parent).ok_or(SummaryBlocker::UnsupportedContext)?.clone()
            }
        };
        let target =
            model.caller.get_mut(&binding.target).ok_or(SummaryBlocker::UnsupportedContext)?;
        *target = value.clone();
        let child = model.callee.get_mut(key).ok_or(SummaryBlocker::UnsupportedContext)?;
        *child = value;
    }
    Ok(Some(model))
}

fn seeded_model(
    field: &FieldContext,
    keys: &BTreeSet<AccessKey>,
    seeds: &BTreeMap<AccessKey, FieldValue>,
) -> BTreeMap<AccessKey, FieldValue> {
    let mut model = BTreeMap::new();
    for key in keys {
        model.insert(
            key.clone(),
            seeds.get(key).cloned().unwrap_or_else(|| field.canonical(0.into())),
        );
    }
    model
}

fn set_representation(
    field: &FieldContext,
    equations: &ClosureEquations<'_>,
    model: &mut ComponentModelAssignment,
    representation: &BitRepresentation,
) -> Result<(), SummaryBlocker> {
    for (key, bit) in equations.relation.bits().iter().zip(representation.bits()) {
        let value = model.callee.get_mut(key).ok_or(SummaryBlocker::UnsupportedContext)?;
        *value = field.canonical(i32::from(*bit).into());
    }
    for (key, value) in &mut model.caller {
        if let Some(child) = equations.ports.child_key(key) {
            *value = model.callee.get(child).ok_or(SummaryBlocker::UnsupportedContext)?.clone();
        }
    }
    Ok(())
}

fn validate_closure(
    field: &FieldContext,
    equations: &ClosureEquations<'_>,
    assignments: &[ComponentModelAssignment; 2],
    budget: &mut ProofBudget,
) -> Result<bool, SummaryBlocker> {
    let caller = [&assignments[0].caller, &assignments[1].caller];
    if !generated_models_satisfy(field, equations.caller, &caller, budget)
        .map_err(SummaryBlocker::LocalFacts)?
    {
        return Ok(false);
    }
    let callee = [&assignments[0].callee, &assignments[1].callee];
    generated_models_satisfy(field, equations.callee, &callee, budget)
        .map_err(SummaryBlocker::LocalFacts)
}

fn no_certificate(reason: NoBitAmbiguityCertificate) -> ComponentBitAmbiguityOutcome {
    ComponentBitAmbiguityOutcome::NoCertificate(reason)
}
