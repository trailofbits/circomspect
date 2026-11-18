//! Checked alternate roots for reachable witness-only assignments in a leaf main scope.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{FlowGraph, NodeId};

use crate::hir_cfg::{CfgNodeKind, Origin};
use crate::hir_facts::relations::polynomial::witness_equation;
use crate::hir_facts::relations::NormalizationInputs;
use crate::hir_facts::{
    generated_models_satisfy, generated_seeds, AccessKey, AnalysisFacts, DescribeSignalAssignment,
    Fact, FactBlocker, FieldValue, GeneratedAssignments, GeneratedEquationSites,
    NormalizedEquation, ProofBudget, SourceSignalAssignment,
};

/// Two distinct values for one witness target with identical external inputs.
#[derive(Clone)]
pub(crate) struct WitnessAlternative {
    pub(crate) target: AccessKey,
    pub(crate) witnessed: FieldValue,
    pub(crate) alternate: FieldValue,
    pub(crate) constraint_origin: Origin,
}

struct CandidateScope<'a, 'facts> {
    target: AccessKey,
    relation: NormalizedEquation,
    generated: &'a GeneratedEquationSites<'facts>,
    completion: GeneratedAssignments<'a>,
    keys: BTreeSet<AccessKey>,
    witness_relations: Vec<(NodeId, NormalizedEquation)>,
    seeds: BTreeMap<AccessKey, FieldValue>,
}

struct WitnessCandidate {
    target: AccessKey,
    relation: NormalizedEquation,
    path: BTreeSet<NodeId>,
}

impl AnalysisFacts<'_> {
    pub(crate) fn local_witness_alternative(
        &self,
        witness: NodeId,
        budget: &mut ProofBudget,
    ) -> Fact<Option<WitnessAlternative>> {
        match self.witness_alternative_result(witness, budget) {
            Ok(result) => Fact::known(result),
            Err(blockers) => Fact::blocked(blockers),
        }
    }

    fn witness_alternative_result(
        &self,
        witness: NodeId,
        budget: &mut ProofBudget,
    ) -> Result<Option<WitnessAlternative>, BTreeSet<FactBlocker>> {
        let Some(WitnessCandidate { target, relation, path }) =
            self.candidate_witness(witness, budget)?
        else {
            return Ok(None);
        };
        let generated = self.generated_equation_sites(budget);
        let generated = generated.as_result().map_err(Clone::clone)?;
        if !generated.keys().contains(&target) {
            return Ok(None);
        }
        let mut keys = generated.keys().clone();
        keys.extend(relation.accesses().into_iter().cloned());
        let witness_relations = self.all_witness_relations(&path, &mut keys, Some(witness))?;
        self.check_model_keys(&keys)?;
        checked_generated_path(generated, &path)?;
        let completion = self.generated_assignments(generated, budget)?;
        let Some(seeds) = generated_seeds(self.field, generated, budget)? else {
            return Ok(None);
        };
        CandidateScope { target, relation, generated, completion, keys, witness_relations, seeds }
            .search(self, budget)
    }

    fn candidate_witness(
        &self,
        witness: NodeId,
        budget: &mut ProofBudget,
    ) -> Result<Option<WitnessCandidate>, BTreeSet<FactBlocker>> {
        let checked = self.must_equation_for_witness(witness);
        if checked.as_result().map_err(Clone::clone)?.is_some() {
            return Ok(None);
        }
        if self.must_execute(witness).as_result().map_err(Clone::clone)? != &true {
            return Ok(None);
        }
        let Some((target, relation)) = self.witness_relation_for_model(witness)? else {
            return Ok(None);
        };
        let path = self.unique_generation_path(budget)?;
        Ok(path.contains(&witness).then_some(WitnessCandidate { target, relation, path }))
    }

    pub(crate) fn witness_relation_for_model(
        &self,
        witness: NodeId,
    ) -> Result<Option<(AccessKey, crate::hir_facts::NormalizedEquation)>, BTreeSet<FactBlocker>>
    {
        let node =
            self.cfg.node(witness).ok_or_else(|| BTreeSet::from([FactBlocker::ForeignQuery]))?;
        let CfgNodeKind::Witness { target, value } = &node.kind else {
            return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        let Some(state) = self.site_state(witness) else { return Ok(None) };
        let Some(values) = state.variables() else { return Ok(None) };
        let Some(symbolic) = state.symbolic() else { return Ok(None) };
        let inputs =
            NormalizationInputs::new(self.hir, self.field, values, self.calls.as_deref(), symbolic);
        let relation = witness_equation(&inputs, target, *value)
            .map_err(|_| BTreeSet::from([FactBlocker::OpaqueExpression(*value)]))?;
        let key = self.exact_access_key_at(target, witness);
        Ok(Some((key.as_result().map_err(Clone::clone)?.clone(), relation)))
    }

    pub(crate) fn all_witness_relations(
        &self,
        path: &BTreeSet<NodeId>,
        keys: &mut BTreeSet<AccessKey>,
        primary: Option<NodeId>,
    ) -> Result<Vec<(NodeId, NormalizedEquation)>, BTreeSet<FactBlocker>> {
        let mut relations = Vec::new();
        for id in path {
            let Some(node) = self.cfg.node(*id) else {
                return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
            };
            let CfgNodeKind::Witness { .. } = &node.kind else { continue };
            let Some(origin) = node.origin else { continue };
            let effect = self
                .hir
                .block(origin.block)
                .and_then(|block| block.effects.get(origin.effect_index));
            let Some(SourceSignalAssignment::Witness { .. }) =
                effect.and_then(DescribeSignalAssignment::signal_assignment)
            else {
                continue;
            };
            if Some(*id) != primary {
                self.must_equation_for_witness(*id).as_result().map_err(Clone::clone)?;
            }
            let Some((target, relation)) = self.witness_relation_for_model(*id)? else {
                return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(*id)]));
            };
            keys.insert(target);
            keys.extend(relation.accesses().into_iter().cloned());
            relations.push((*id, relation));
        }
        Ok(relations)
    }
}

pub(crate) fn checked_generated_path(
    generated: &GeneratedEquationSites<'_>,
    path: &BTreeSet<NodeId>,
) -> Result<(), BTreeSet<FactBlocker>> {
    for site in generated.sites() {
        if !path.contains(&site.site()) {
            return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(site.site())]));
        }
    }
    Ok(())
}

impl CandidateScope<'_, '_> {
    fn search(
        &self,
        facts: &AnalysisFacts<'_>,
        budget: &mut ProofBudget,
    ) -> Result<Option<WitnessAlternative>, BTreeSet<FactBlocker>> {
        for input_seed in [0, 1] {
            let Some(model) = self.baseline(facts, input_seed, budget)? else { continue };
            if let Some(alternative) = self.alternate(facts, &model, budget)? {
                return Ok(Some(alternative));
            }
        }
        Ok(None)
    }

    fn baseline(
        &self,
        facts: &AnalysisFacts<'_>,
        input_seed: i32,
        budget: &mut ProofBudget,
    ) -> Result<Option<BTreeMap<AccessKey, FieldValue>>, BTreeSet<FactBlocker>> {
        let mut model = seeded_model(facts, &self.keys, &self.seeds, input_seed);
        if !solve_witness(facts, &self.relation, &self.target, &mut model, budget)? {
            return Ok(None);
        }
        if !self.completion.complete(facts.field, &mut model, budget)? {
            return Ok(None);
        }
        if !witness_relations_hold(facts, &self.witness_relations, &model, budget)? {
            return Ok(None);
        }
        if !generated_models_satisfy(facts.field, self.generated, &[&model], budget)? {
            return Ok(None);
        }
        Ok(Some(model))
    }

    fn alternate(
        &self,
        facts: &AnalysisFacts<'_>,
        model: &BTreeMap<AccessKey, FieldValue>,
        budget: &mut ProofBudget,
    ) -> Result<Option<WitnessAlternative>, BTreeSet<FactBlocker>> {
        let witnessed = model[&self.target].clone();
        for site in self.generated.sites() {
            if !budget.reserve_evaluation(site.equation()) {
                return Err(BTreeSet::from([FactBlocker::Budget(site.site())]));
            }
            let alternate = site
                .equation()
                .alternate_quadratic_root(facts.field, model, &self.target, &witnessed)
                .map_err(|_| BTreeSet::from([FactBlocker::UnsupportedRelation(site.site())]))?;
            let Some(alternate) = alternate else { continue };
            let mut second = model.clone();
            second.insert(self.target.clone(), alternate.clone());
            if !self.completion.complete(facts.field, &mut second, budget)?
                || second.get(&self.target) != Some(&alternate)
            {
                continue;
            }
            if generated_models_satisfy(facts.field, self.generated, &[&second], budget)? {
                return Ok(Some(WitnessAlternative {
                    target: self.target.clone(),
                    witnessed,
                    alternate,
                    constraint_origin: site.origin(),
                }));
            }
        }
        Ok(None)
    }
}

pub(crate) fn witness_relations_hold(
    facts: &AnalysisFacts<'_>,
    relations: &[(NodeId, NormalizedEquation)],
    model: &BTreeMap<AccessKey, FieldValue>,
    budget: &mut ProofBudget,
) -> Result<bool, BTreeSet<FactBlocker>> {
    for (id, relation) in relations {
        if !budget.reserve_evaluation(relation) {
            return Err(BTreeSet::from([FactBlocker::Budget(*id)]));
        }
        let value = relation
            .evaluate(facts.field, model)
            .map_err(|_| BTreeSet::from([FactBlocker::UnsupportedRelation(*id)]))?;
        if !facts.field.is_zero(&value) {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(crate) fn seeded_model(
    facts: &AnalysisFacts<'_>,
    keys: &BTreeSet<AccessKey>,
    seeds: &BTreeMap<AccessKey, FieldValue>,
    input_seed: i32,
) -> BTreeMap<AccessKey, FieldValue> {
    keys.iter()
        .map(|key| {
            let value =
                seeds.get(key).cloned().unwrap_or_else(|| facts.field.canonical(input_seed.into()));
            (key.clone(), value)
        })
        .collect()
}

fn solve_witness(
    facts: &AnalysisFacts<'_>,
    relation: &crate::hir_facts::NormalizedEquation,
    target: &AccessKey,
    model: &mut BTreeMap<AccessKey, FieldValue>,
    budget: &mut ProofBudget,
) -> Result<bool, BTreeSet<FactBlocker>> {
    if !budget.reserve_evaluation(relation) {
        return Err(BTreeSet::from([FactBlocker::Budget(facts.cfg.entry())]));
    }
    let value = relation
        .solve_linear_target(facts.field, model, target)
        .map_err(|_| BTreeSet::from([FactBlocker::UnsupportedRelation(facts.cfg.entry())]))?;
    let Some(value) = value else { return Ok(false) };
    model.insert(target.clone(), value);
    Ok(true)
}
