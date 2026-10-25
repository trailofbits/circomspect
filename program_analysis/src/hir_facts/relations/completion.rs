//! Deterministic candidate completion for source-owned generated assignments.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{FlowGraph, NodeId};
use parser::hir::SymbolKind;
use parser::new_frontend::PortDirection;

use crate::hir_cfg::{CfgNodeKind, Constraint};
use crate::hir_facts::relations::complete::{GeneratedConstraintSite, GeneratedEquationSites};
use crate::hir_facts::{
    AccessKey, AnalysisFacts, DescribeSignalAssignment, FactBlocker, FieldContext, FieldValue,
    NormalizedEquation, SourceSignalAssignment, ProofBudget,
};

struct GeneratedAssignment<'a> {
    site: NodeId,
    target: AccessKey,
    equation: &'a NormalizedEquation,
    dependencies: BTreeSet<AccessKey>,
}

/// A finite dependency order; it never assigns external inputs or component ports.
pub(crate) struct GeneratedAssignments<'a> {
    ordered: Vec<GeneratedAssignment<'a>>,
}

impl GeneratedAssignments<'_> {
    /// Complete only generated assignment targets, keeping all other values fixed.
    ///
    /// Returns false if a unique linear completion is unavailable. Every generated
    /// equation must still be validated after this candidate-only operation.
    pub(crate) fn complete(
        &self,
        field: &FieldContext,
        model: &mut BTreeMap<AccessKey, FieldValue>,
        budget: &mut ProofBudget,
    ) -> Result<bool, BTreeSet<FactBlocker>> {
        for assignment in &self.ordered {
            if !budget.reserve_evaluation(assignment.equation)
                || !budget.reserve_evaluation(assignment.equation)
            {
                return Err(BTreeSet::from([FactBlocker::Budget(assignment.site)]));
            }
            let value =
                assignment.equation.solve_linear_target(field, model, &assignment.target).map_err(
                    |_| BTreeSet::from([FactBlocker::UnsupportedRelation(assignment.site)]),
                )?;
            let Some(value) = value else { return Ok(false) };
            let Some(target) = model.get_mut(&assignment.target) else {
                return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(assignment.site)]));
            };
            *target = value;
        }
        Ok(true)
    }
}

impl AnalysisFacts<'_> {
    pub(crate) fn generated_assignments<'a>(
        &self,
        sites: &'a GeneratedEquationSites<'_>,
        budget: &mut ProofBudget,
    ) -> Result<GeneratedAssignments<'a>, BTreeSet<FactBlocker>> {
        if self.evidence_binding.as_ref() != Some(sites.evidence()) {
            return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        let mut pending = BTreeMap::new();
        for site in sites.sites() {
            if !budget.reserve_control_step() {
                return Err(BTreeSet::from([FactBlocker::Budget(site.site())]));
            }
            let Some(target) = self.local_generated_target(site)? else { continue };
            if !budget.reserve_key() || !budget.reserve_evaluation(site.equation()) {
                return Err(BTreeSet::from([FactBlocker::Budget(site.site())]));
            }
            let dependencies = site
                .equation()
                .accesses()
                .into_iter()
                .filter(|key| **key != target)
                .cloned()
                .collect();
            let entry = GeneratedAssignment {
                site: site.site(),
                target: target.clone(),
                equation: site.equation(),
                dependencies,
            };
            if pending.insert(target, entry).is_some() {
                return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(site.site())]));
            }
        }
        order_assignments(pending, budget)
    }

    fn local_generated_target(
        &self,
        site: &GeneratedConstraintSite<'_>,
    ) -> Result<Option<AccessKey>, BTreeSet<FactBlocker>> {
        let foreign = || BTreeSet::from([FactBlocker::ForeignQuery]);
        let node = self.cfg.node(site.site()).ok_or_else(foreign)?;
        let CfgNodeKind::Constraint(Constraint::Assignment { target, value: generated_value }) =
            &node.kind
        else {
            return Ok(None);
        };
        let origin = site.origin();
        let effect = self
            .hir
            .block(origin.block)
            .and_then(|block| block.effects.get(origin.effect_index))
            .ok_or_else(foreign)?;
        let Some(SourceSignalAssignment::Generated { target: source, value }) =
            effect.signal_assignment()
        else {
            return Err(foreign());
        };
        if source != target || value != *generated_value || node.origin != Some(origin) {
            return Err(foreign());
        }
        let symbol = self.hir.symbol(target.root).ok_or_else(foreign)?;
        if symbol.kind != SymbolKind::Signal || target.component_input || target.component_output {
            return Ok(None);
        }
        if self
            .hir
            .ports()
            .iter()
            .any(|port| port.symbol == target.root && port.direction == Some(PortDirection::Input))
        {
            return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(site.site())]));
        }
        let key = self.exact_access_key_at(target, site.site());
        key.certified()
            .cloned()
            .map(Some)
            .ok_or_else(|| key.unavailable().cloned().unwrap_or_else(foreign))
    }
}

fn order_assignments<'a>(
    mut pending: BTreeMap<AccessKey, GeneratedAssignment<'a>>,
    budget: &mut ProofBudget,
) -> Result<GeneratedAssignments<'a>, BTreeSet<FactBlocker>> {
    let mut ordered = Vec::new();
    while !pending.is_empty() {
        let Some(key) = next_assignment(&pending, budget)? else {
            return Err(pending
                .values()
                .map(|item| FactBlocker::UnsupportedRelation(item.site))
                .collect());
        };
        let Some(entry) = pending.remove(&key) else {
            return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        ordered.push(entry);
    }
    Ok(GeneratedAssignments { ordered })
}

fn next_assignment(
    pending: &BTreeMap<AccessKey, GeneratedAssignment<'_>>,
    budget: &mut ProofBudget,
) -> Result<Option<AccessKey>, BTreeSet<FactBlocker>> {
    for (key, entry) in pending {
        if !budget.reserve_evaluation(entry.equation) {
            return Err(BTreeSet::from([FactBlocker::Budget(entry.site)]));
        }
        if entry.dependencies.iter().all(|dependency| !pending.contains_key(dependency)) {
            return Ok(Some(key.clone()));
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests;
