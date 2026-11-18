//! Checked zero models for reachable witness divisions in a leaf main scope.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{FlowGraph, NodeId};
use parser::frontend::{BinaryOperator, UnaryOperator};
use parser::hir::{AccessPath, ExprKind};

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::relations::witness_alternative::{
    checked_generated_path, seeded_model, witness_relations_hold,
};
use crate::hir_facts::{
    generated_models_satisfy, generated_seeds, AccessKey, AnalysisFacts, Fact, FactBlocker,
    DescribeSignalAssignment, FieldValue, GeneratedAssignments, GeneratedEquationSites,
    NormalizedEquation, ProofBudget, SourceSignalAssignment,
};

/// A zero input and complete assignment satisfying every generated equation.
#[derive(Clone)]
pub(crate) struct FeasibleZeroDivisor {
    pub(crate) divisor: AccessKey,
    pub(crate) constraint_count: usize,
}

struct ZeroModelScope<'a, 'facts> {
    divisor: AccessKey,
    generated: &'a GeneratedEquationSites<'facts>,
    completion: GeneratedAssignments<'a>,
    keys: BTreeSet<AccessKey>,
    siblings: Vec<(NodeId, NormalizedEquation)>,
    seeds: BTreeMap<AccessKey, FieldValue>,
}

impl AnalysisFacts<'_> {
    pub(crate) fn local_feasible_zero_divisor(
        &self,
        witness: NodeId,
        divisor: &AccessPath,
        budget: &mut ProofBudget,
    ) -> Fact<Option<FeasibleZeroDivisor>> {
        match self.zero_divisor_result(witness, divisor, budget) {
            Ok(result) => Fact::known(result),
            Err(blockers) => Fact::blocked(blockers),
        }
    }

    fn zero_divisor_result(
        &self,
        witness: NodeId,
        divisor: &AccessPath,
        budget: &mut ProofBudget,
    ) -> Result<Option<FeasibleZeroDivisor>, BTreeSet<FactBlocker>> {
        if !self.checked_division_witness(witness, divisor)? {
            return Ok(None);
        }
        let divisor = self.exact_access_key_at(divisor, witness);
        let divisor = divisor.as_result().map_err(Clone::clone)?.clone();
        let readiness = self.body_signal_reads_ready();
        if let Some(blockers) = readiness.unavailable() {
            return Err(blockers.clone());
        }
        let path = self.unique_generation_path(budget)?;
        if !path.contains(&witness) {
            return Ok(None);
        }
        self.check_evaluations_before_division(witness, &path)?;
        let generated = self.generated_equation_sites(budget);
        let generated = generated.as_result().map_err(Clone::clone)?;
        if !generated.keys().contains(&divisor) {
            return Ok(None);
        }
        checked_generated_path(generated, &path)?;
        let mut keys = generated.keys().clone();
        let siblings = self.other_witness_relations(&path, witness, &mut keys)?;
        self.check_model_keys(&keys)?;
        let completion = self.generated_assignments(generated, budget)?;
        let Some(seeds) = generated_seeds(self.field, generated, budget)? else { return Ok(None) };
        ZeroModelScope { divisor, generated, completion, keys, siblings, seeds }
            .search(self, budget)
    }

    fn checked_division_witness(
        &self,
        witness: NodeId,
        divisor: &AccessPath,
    ) -> Result<bool, BTreeSet<FactBlocker>> {
        let node = self.cfg.node(witness).ok_or_else(foreign)?;
        let CfgNodeKind::Witness { target, value } = &node.kind else { return Err(foreign()) };
        let origin = node.origin.ok_or_else(foreign)?;
        let effect = self
            .hir
            .block(origin.block)
            .and_then(|block| block.effects.get(origin.effect_index))
            .ok_or_else(foreign)?;
        let Some(SourceSignalAssignment::Witness { target: source, value: written }) =
            effect.signal_assignment()
        else {
            return Ok(false);
        };
        if source != target || written != *value {
            return Ok(false);
        }
        let expression = self.hir.expression(*value).ok_or_else(foreign)?;
        let ExprKind::Binary { operator, right, .. } = &expression.kind else { return Ok(false) };
        if *operator != BinaryOperator::Divide && *operator != BinaryOperator::IntegerDivide {
            return Ok(false);
        }
        let denominator = self.hir.expression(*right).ok_or_else(foreign)?;
        let ExprKind::Access(path) = &denominator.kind else { return Ok(false) };
        Ok(path == divisor)
    }

    fn check_evaluations_before_division(
        &self,
        witness: NodeId,
        path: &BTreeSet<NodeId>,
    ) -> Result<(), BTreeSet<FactBlocker>> {
        let node = self.cfg.node(witness).ok_or_else(foreign)?;
        let CfgNodeKind::Witness { value, .. } = &node.kind else { return Err(foreign()) };
        let primary = self.primary_division_evaluation(witness, *value, path)?;
        self.check_preceding_evaluations(witness, primary, path)
    }

    fn primary_division_evaluation(
        &self,
        witness: NodeId,
        value: parser::hir::ExprId,
        path: &BTreeSet<NodeId>,
    ) -> Result<NodeId, BTreeSet<FactBlocker>> {
        let mut primary_evaluation = None;
        for id in self.cfg.edges() {
            let edge = self.cfg.edge(*id).ok_or_else(foreign)?;
            if edge.target != witness || !path.contains(&edge.source) {
                continue;
            }
            let Some(CfgNodeKind::Evaluate(expression)) =
                self.cfg.node(edge.source).map(|node| &node.kind)
            else {
                continue;
            };
            if *expression == value && primary_evaluation.replace(edge.source).is_some() {
                return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(witness)]));
            }
        }
        primary_evaluation
            .ok_or_else(|| BTreeSet::from([FactBlocker::UnsupportedRelation(witness)]))
    }

    fn check_preceding_evaluations(
        &self,
        witness: NodeId,
        primary: NodeId,
        path: &BTreeSet<NodeId>,
    ) -> Result<(), BTreeSet<FactBlocker>> {
        let preceding = self.cfg.reaching_candidates(&BTreeSet::from([witness]), path);
        for site in preceding {
            if site == primary {
                continue;
            }
            let Some(CfgNodeKind::Evaluate(expression)) =
                self.cfg.node(site).map(|node| &node.kind)
            else {
                continue;
            };
            let expression = self.hir.expression(*expression).ok_or_else(foreign)?;
            if !safe_preceding_expression(&expression.kind) {
                return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(site)]));
            }
        }
        Ok(())
    }

    fn other_witness_relations(
        &self,
        path: &BTreeSet<NodeId>,
        primary: NodeId,
        keys: &mut BTreeSet<AccessKey>,
    ) -> Result<Vec<(NodeId, NormalizedEquation)>, BTreeSet<FactBlocker>> {
        let mut relations = Vec::new();
        for site in path {
            if *site == primary {
                continue;
            }
            let Some(node) = self.cfg.node(*site) else { return Err(foreign()) };
            let CfgNodeKind::Witness { .. } = &node.kind else { continue };
            let Some((target, relation)) = self.other_witness_relation(*site)? else { continue };
            keys.insert(target);
            keys.extend(relation.accesses().into_iter().cloned());
            relations.push((*site, relation));
        }
        Ok(relations)
    }

    fn other_witness_relation(
        &self,
        site: NodeId,
    ) -> Result<Option<(AccessKey, NormalizedEquation)>, BTreeSet<FactBlocker>> {
        let node = self.cfg.node(site).ok_or_else(foreign)?;
        let CfgNodeKind::Witness { target, value } = &node.kind else { return Err(foreign()) };
        let origin = node.origin.ok_or_else(foreign)?;
        let effect = self
            .hir
            .block(origin.block)
            .and_then(|block| block.effects.get(origin.effect_index))
            .ok_or_else(foreign)?;
        match effect.signal_assignment() {
            Some(SourceSignalAssignment::Witness { target: source, value: written })
                if source == target && written == *value => {}
            Some(SourceSignalAssignment::Generated { target: source, value: written })
                if source == target && written == *value =>
            {
                return Ok(None)
            }
            Some(
                SourceSignalAssignment::Generated { .. } | SourceSignalAssignment::Witness { .. },
            )
            | None => return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(site)])),
        }
        self.witness_relation_for_model(site)?
            .map(Some)
            .ok_or_else(|| BTreeSet::from([FactBlocker::UnsupportedRelation(site)]))
    }
}

impl ZeroModelScope<'_, '_> {
    fn search(
        &self,
        facts: &AnalysisFacts<'_>,
        budget: &mut ProofBudget,
    ) -> Result<Option<FeasibleZeroDivisor>, BTreeSet<FactBlocker>> {
        if self.seeds.get(&self.divisor).is_some_and(|value| !facts.field.is_zero(value)) {
            return Ok(None);
        }
        for input_seed in [0, 1] {
            let mut model = seeded_model(facts, &self.keys, &self.seeds, input_seed);
            model.insert(self.divisor.clone(), facts.field.canonical(0.into()));
            if !self.completion.complete(facts.field, &mut model, budget)? {
                continue;
            }
            if !facts.field.is_zero(&model[&self.divisor])
                || !witness_relations_hold(facts, &self.siblings, &model, budget)?
            {
                continue;
            }
            if generated_models_satisfy(facts.field, self.generated, &[&model], budget)? {
                return Ok(Some(FeasibleZeroDivisor {
                    divisor: self.divisor.clone(),
                    constraint_count: self.generated.sites().len(),
                }));
            }
        }
        Ok(None)
    }
}

fn foreign() -> BTreeSet<FactBlocker> {
    BTreeSet::from([FactBlocker::ForeignQuery])
}

fn safe_preceding_expression(kind: &ExprKind) -> bool {
    match kind {
        ExprKind::Access(path) => path.steps.is_empty(),
        ExprKind::Number(_)
        | ExprKind::Parallel(_)
        | ExprKind::Unary { operator: UnaryOperator::Negate, .. }
        | ExprKind::Binary {
            operator: BinaryOperator::Add | BinaryOperator::Subtract | BinaryOperator::Multiply,
            ..
        } => true,
        ExprKind::Unary { .. }
        | ExprKind::Binary { .. }
        | ExprKind::Call { .. }
        | ExprKind::AnonymousComponent { .. }
        | ExprKind::Array(_)
        | ExprKind::Tuple(_)
        | ExprKind::Ternary { .. }
        | ExprKind::Opaque(_) => false,
    }
}

#[cfg(test)]
// Test fixture assembly uses panics and unwraps to keep failed setup visible.
#[allow(clippy::allow_attributes, clippy::panic, clippy::unwrap_used)]
mod tests {
    use std::fs;

    use abstract_interpretation::graph::FlowGraph;
    use parser::frontend::{load_sources, Version, VersionPolicy};
    use parser::hir::{lift_project, ExprKind};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::{build_cfg, CfgNodeKind};
    use crate::hir_facts::ProofBudget;
    use crate::interprocedural::ProjectAnalysis;

    #[test]
    fn zero_model_refuses_exhausted_budget_and_wrong_divisor() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-zero-budget-{}-{:?}",
            std::process::id(),
            std::thread::current().id(),
        ));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(
            &source,
            "pragma circom 2.2.3;template T(){signal input x;signal output y;\
             y <-- 1/x;x*(x-1)===0;y*x===x;}component main=T();",
        )
        .unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let definition = lifted.hir.definition("T").unwrap();
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let evidence = provider.contexts().symbolic_root(definition).unwrap();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let witness = facts
            .cfg()
            .nodes()
            .iter()
            .copied()
            .find(|id| {
                let Some(node) = facts.cfg().node(*id) else { return false };
                let CfgNodeKind::Witness { .. } = &node.kind else { return false };
                true
            })
            .unwrap();
        let node = facts.cfg().node(witness).unwrap();
        let CfgNodeKind::Witness { value, .. } = &node.kind else { panic!("witness") };
        let expression = lifted.hir.expression(*value).unwrap();
        let ExprKind::Binary { right, .. } = &expression.kind else { panic!("division") };
        let denominator = lifted.hir.expression(*right).unwrap();
        let ExprKind::Access(path) = &denominator.kind else { panic!("access") };
        let limited =
            facts.local_feasible_zero_divisor(witness, path, &mut ProofBudget::limited(0, 0, 0, 0));
        assert!(limited.unavailable().is_some());
        let mut other = path.clone();
        other.root = lifted.hir.symbols().iter().find(|symbol| symbol.name == "y").unwrap().id;
        other.terminal = other.root;
        let wrong = facts.local_feasible_zero_divisor(witness, &other, &mut ProofBudget::default());
        assert!(wrong.certified().unwrap().is_none());
    }
}
