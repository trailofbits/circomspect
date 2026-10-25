//! One complete candidate, with fixed-input evidence separate from default choices.

use std::collections::BTreeMap;

use parser::new_frontend::Span;

use crate::hir_facts::{
    generated_models_satisfy, generated_seeds, AccessKey, BitRepresentation,
    DescribeSignalAssignment, FieldContext, SourceSignalAssignment, FieldValue, ProofBudget,
};
use crate::interprocedural::comparator_range::{
    ComparatorClosure, ComparatorRangeViolation, ComparatorScope,
};
use crate::interprocedural::input_relation::ReadyGeneratedInputs;
use crate::interprocedural::{AppliedComponentPort, SummaryBlocker};

type Model = BTreeMap<AccessKey, FieldValue>;

struct ComparatorModels {
    main: Model,
    comparison: Model,
    decomposition: Model,
}

pub(super) fn validate_candidate(
    field: &FieldContext,
    applied: &AppliedComponentPort,
    closure: &ComparatorClosure<'_>,
    budget: &mut ProofBudget,
) -> Result<Vec<ComparatorRangeViolation>, SummaryBlocker> {
    let Some(main_seeds) =
        generated_seeds(field, closure.main.sites, budget).map_err(SummaryBlocker::LocalFacts)?
    else {
        return Ok(Vec::new());
    };
    let mut violations = fixed_violations(field, applied, closure, &main_seeds, budget)?;
    if violations.is_empty() {
        return Ok(violations);
    }
    let Some(mut models) = build_candidates(field, closure, budget)? else { return Ok(Vec::new()) };
    if !complete_candidates(field, closure, &mut models, budget)?
        || !check_candidates(field, closure, &models, budget)?
    {
        return Ok(Vec::new());
    }
    let origins = constraint_origins(closure);
    for violation in &mut violations {
        violation.origins.clone_from(&origins);
    }
    Ok(violations)
}

fn build_candidates(
    field: &FieldContext,
    closure: &ComparatorClosure<'_>,
    budget: &mut ProofBudget,
) -> Result<Option<ComparatorModels>, SummaryBlocker> {
    let Some(mut main) = seed_model(field, &closure.main, budget)? else { return Ok(None) };
    let Some(mut comparison) = seed_model(field, &closure.comparison, budget)? else {
        return Ok(None);
    };
    let Some(mut decomposition) = seed_model(field, &closure.decomposition, budget)? else {
        return Ok(None);
    };
    if !complete_inputs(field, closure.main_ready, &mut main, &mut comparison, budget)?
        || !complete_inputs(
            field,
            closure.comparison_ready,
            &mut comparison,
            &mut decomposition,
            budget,
        )?
    {
        return Ok(None);
    }
    if !install_bits(field, closure, &mut decomposition)? {
        return Ok(None);
    }
    Ok(Some(ComparatorModels { main, comparison, decomposition }))
}

fn install_bits(
    field: &FieldContext,
    closure: &ComparatorClosure<'_>,
    decomposition: &mut Model,
) -> Result<bool, SummaryBlocker> {
    let relation = &closure.pattern.relation;
    let input = decomposition.get(relation.input()).ok_or(SummaryBlocker::MissingInputBinding)?;
    let integer = input.as_bigint().to_biguint().ok_or(SummaryBlocker::UnsupportedContext)?;
    let Some(bits) = BitRepresentation::new(integer, relation.bits().len()) else {
        return Ok(false);
    };
    for (key, bit) in relation.bits().iter().zip(bits.bits()) {
        *decomposition.get_mut(key).ok_or(SummaryBlocker::UnsupportedContext)? =
            field.canonical(i32::from(*bit).into());
    }
    Ok(true)
}

fn complete_candidates(
    field: &FieldContext,
    closure: &ComparatorClosure<'_>,
    models: &mut ComparatorModels,
    budget: &mut ProofBudget,
) -> Result<bool, SummaryBlocker> {
    let ComparatorModels { main, comparison, decomposition } = models;
    mirror_outputs(closure.comparison_ready, decomposition, comparison)?;
    if !complete_outputs(field, &closure.comparison, comparison, budget)? {
        return Ok(false);
    }
    mirror_outputs(closure.main_ready, comparison, main)?;
    if !complete_outputs(field, &closure.main, main, budget)? {
        return Ok(false);
    }
    Ok(true)
}

fn check_candidates(
    field: &FieldContext,
    closure: &ComparatorClosure<'_>,
    models: &ComparatorModels,
    budget: &mut ProofBudget,
) -> Result<bool, SummaryBlocker> {
    let ComparatorModels { main, comparison, decomposition } = models;
    for (scope, model) in [
        (&closure.main, main),
        (&closure.comparison, comparison),
        (&closure.decomposition, decomposition),
    ] {
        if !generated_models_satisfy(field, scope.sites, &[model], budget)
            .map_err(SummaryBlocker::LocalFacts)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn constraint_origins(closure: &ComparatorClosure<'_>) -> Vec<crate::hir_cfg::Origin> {
    let mut origins = Vec::new();
    for scope in [&closure.main, &closure.comparison, &closure.decomposition] {
        for site in scope.sites.sites() {
            origins.push(site.origin());
        }
    }
    origins
}

fn fixed_violations(
    field: &FieldContext,
    applied: &AppliedComponentPort,
    closure: &ComparatorClosure<'_>,
    seeds: &Model,
    budget: &mut ProofBudget,
) -> Result<Vec<ComparatorRangeViolation>, SummaryBlocker> {
    let mut results = Vec::new();
    for (element, binding) in closure.main_ready.bindings() {
        let local =
            closure.main_ready.ports().input_key(element).ok_or(SummaryBlocker::WrongInstance)?;
        if !closure.pattern.inputs.contains(local) {
            continue;
        }
        if !budget.reserve_evaluation(binding.value.equation())
            || !budget.reserve_evaluation(binding.value.equation())
        {
            return Err(SummaryBlocker::ContextBudget);
        }
        let value =
            binding.value.equation().solve_linear_target(field, seeds, binding.value.target());
        let Ok(Some(value)) = value else { continue };
        if value.as_bigint() < &closure.pattern.bound {
            continue;
        }
        let origin = binding.origins.first().ok_or(SummaryBlocker::UnsupportedContext)?;
        let span = binding_span(&closure.main, *origin)?;
        results.push(ComparatorRangeViolation {
            applied: applied.clone(),
            decomposition: closure.pattern.relation.clone(),
            input: binding.target.clone(),
            value,
            bound: closure.pattern.bound.clone(),
            span,
            origins: Vec::new(),
        });
    }
    Ok(results)
}

fn binding_span(
    scope: &ComparatorScope<'_>,
    origin: crate::hir_cfg::Origin,
) -> Result<Span, SummaryBlocker> {
    let effect = scope
        .facts
        .hir()
        .block(origin.block)
        .and_then(|block| block.effects.get(origin.effect_index));
    let Some(SourceSignalAssignment::Generated { value, .. }) =
        effect.and_then(DescribeSignalAssignment::signal_assignment)
    else {
        return Err(SummaryBlocker::UnsupportedContext);
    };
    Ok(scope.facts.hir().expression(value).ok_or(SummaryBlocker::UnsupportedContext)?.span)
}

fn seed_model(
    field: &FieldContext,
    scope: &ComparatorScope<'_>,
    budget: &mut ProofBudget,
) -> Result<Option<Model>, SummaryBlocker> {
    let Some(seeds) =
        generated_seeds(field, scope.sites, budget).map_err(SummaryBlocker::LocalFacts)?
    else {
        return Ok(None);
    };
    let mut model = BTreeMap::new();
    for key in scope.sites.keys() {
        if !budget.reserve_key() {
            return Err(SummaryBlocker::ContextBudget);
        }
        model.insert(
            key.clone(),
            seeds.get(key).cloned().unwrap_or_else(|| field.canonical(0.into())),
        );
    }
    Ok(Some(model))
}

fn complete_inputs(
    field: &FieldContext,
    ready: &ReadyGeneratedInputs,
    parent: &mut Model,
    child: &mut Model,
    budget: &mut ProofBudget,
) -> Result<bool, SummaryBlocker> {
    for (element, binding) in ready.bindings() {
        let equation = binding.value.equation();
        if !budget.reserve_evaluation(equation) || !budget.reserve_evaluation(equation) {
            return Err(SummaryBlocker::ContextBudget);
        }
        let Some(value) = equation
            .solve_linear_target(field, parent, &binding.target)
            .map_err(|_| SummaryBlocker::UnsupportedContext)?
        else {
            return Ok(false);
        };
        let local = ready.ports().input_key(element).ok_or(SummaryBlocker::WrongInstance)?;
        *parent.get_mut(&binding.target).ok_or(SummaryBlocker::UnsupportedContext)? = value.clone();
        *child.get_mut(local).ok_or(SummaryBlocker::UnsupportedContext)? = value;
    }
    Ok(true)
}

fn mirror_outputs(
    ready: &ReadyGeneratedInputs,
    child: &Model,
    parent: &mut Model,
) -> Result<(), SummaryBlocker> {
    for (key, value) in parent {
        if let Some(local) = ready.ports().child_key(key) {
            *value = child.get(local).ok_or(SummaryBlocker::UnsupportedContext)?.clone();
        }
    }
    Ok(())
}

fn complete_outputs(
    field: &FieldContext,
    scope: &ComparatorScope<'_>,
    model: &mut Model,
    budget: &mut ProofBudget,
) -> Result<bool, SummaryBlocker> {
    scope
        .facts
        .generated_assignments(scope.sites, budget)
        .and_then(|completion| completion.complete(field, model, budget))
        .map_err(SummaryBlocker::LocalFacts)
}
