//! Name-independent generated affine, Boolean reconstruction and output relations.

use num_bigint::BigInt;

use crate::hir_facts::{AccessKey, BitDecomposition, FieldContext, ProofBudget};
use crate::interprocedural::comparator_range::source::bit_handles;
use crate::interprocedural::comparator_range::ComparatorScope;
use crate::interprocedural::input_relation::ReadyGeneratedInputs;
use crate::interprocedural::summary::certified;
use crate::interprocedural::{AppliedComponentPort, SummaryBlocker};

pub(super) struct ComparatorPattern {
    pub inputs: [AccessKey; 2],
    pub relation: BitDecomposition,
    pub bound: BigInt,
}

impl ComparatorPattern {
    pub(super) fn find(
        field: &FieldContext,
        applied: &AppliedComponentPort,
        scopes: [&ComparatorScope<'_>; 2],
        ready: &ReadyGeneratedInputs,
        budget: &mut ProofBudget,
    ) -> Result<Option<Self>, SummaryBlocker> {
        let [comparison, decomposition] = scopes;
        if ready.bindings().len() != 1 {
            return Ok(None);
        }
        let (port, binding) =
            ready.bindings().iter().next().ok_or(SummaryBlocker::MissingInputBinding)?;
        let input = decomposition
            .facts
            .port_handle(port.port(), port.indices())
            .map_err(|_| SummaryBlocker::UnsupportedContext)?;
        let bits = bit_handles(decomposition.facts)?;
        let relation = decomposition.facts.bit_decomposition_handles(&input, &bits);
        let Some(relation) = certified(&relation)? else { return Ok(None) };
        let bound = BigInt::from(1) << (relation.bits().len() - 1);
        if &bound * 2 >= *field.modulus() {
            return Ok(None);
        }
        let inputs = comparison_inputs(comparison)?;
        let [left, right] = inputs.as_slice() else { return Ok(None) };
        let target = binding.value.target();
        let mut ordered = None;
        for (a, b) in [(left, right), (right, left)] {
            if !budget.reserve_evaluation(binding.value.equation()) {
                return Err(SummaryBlocker::ContextBudget);
            }
            let terms = [(target.clone(), 1), (a.clone(), -1), (b.clone(), 1)];
            if binding
                .value
                .equation()
                .matches_linear_relation(field, -bound.clone(), &terms)
                .map_err(|_| SummaryBlocker::UnsupportedContext)?
            {
                ordered = Some([a.clone(), b.clone()]);
            }
        }
        let Some(inputs) = ordered else { return Ok(None) };
        if !output_relation(field, applied, comparison, (relation, ready), budget)? {
            return Ok(None);
        }
        Ok(Some(Self { inputs, relation: relation.clone(), bound }))
    }
}

fn comparison_inputs(scope: &ComparatorScope<'_>) -> Result<Vec<AccessKey>, SummaryBlocker> {
    let parser::hir::DefinitionRef::Template(id) = scope.facts.definition() else {
        return Err(SummaryBlocker::WrongInstance);
    };
    let template = scope.facts.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
    let mut keys = Vec::new();
    for id in &template.ports {
        let port = scope.facts.hir().port(*id).ok_or(SummaryBlocker::ForeignDefinition)?;
        if port.direction != Some(parser::new_frontend::PortDirection::Input) {
            continue;
        }
        let dimensions = scope
            .facts
            .checked_symbol_dimensions(port.symbol)
            .map_err(|_| SummaryBlocker::UnsupportedContext)?;
        let indices = crate::interprocedural::output_enumeration::checked_indices(
            &dimensions,
            2 - keys.len(),
        )?;
        for indices in indices {
            let handle = scope
                .facts
                .port_handle(port.id, &indices)
                .map_err(|_| SummaryBlocker::UnsupportedContext)?;
            keys.push(certified(&scope.facts.exact_handle_key(&handle))?.clone());
        }
    }
    Ok(keys)
}

fn output_relation(
    field: &FieldContext,
    applied: &AppliedComponentPort,
    comparison: &ComparatorScope<'_>,
    nested: (&BitDecomposition, &ReadyGeneratedInputs),
    budget: &mut ProofBudget,
) -> Result<bool, SummaryBlocker> {
    let (relation, ready) = nested;
    let high = relation.bits().last().ok_or(SummaryBlocker::UnsupportedContext)?;
    let high = ready.ports().parent_key(high).ok_or(SummaryBlocker::WrongInstance)?;
    let (port, indices) = applied.handle().output_port().ok_or(SummaryBlocker::WrongInstance)?;
    if !indices.is_empty() {
        return Ok(false);
    }
    let handle =
        comparison.facts.port_handle(port, &[]).map_err(|_| SummaryBlocker::UnsupportedContext)?;
    let output = certified(&comparison.facts.exact_handle_key(&handle))?.clone();
    let terms = [(output, 1), (high.clone(), 1)];
    for site in comparison.sites.sites() {
        if !budget.reserve_evaluation(site.equation()) {
            return Err(SummaryBlocker::ContextBudget);
        }
        if site
            .equation()
            .matches_linear_relation(field, (-1).into(), &terms)
            .map_err(|_| SummaryBlocker::UnsupportedContext)?
        {
            return Ok(true);
        }
    }
    Ok(false)
}
