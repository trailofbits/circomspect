//! Checked non-Boolean values for scalar signals declaring the binary tag.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::FlowGraph;
use parser::frontend::PortDirection;
use parser::hir::SymbolId;

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::relations::polynomial::boolean_equation;
use crate::hir_facts::relations::witness_alternative::{
    checked_generated_path, seeded_model, witness_relations_hold,
};
use crate::hir_facts::{
    generated_models_satisfy, generated_seeds, AccessKey, AnalysisFacts, Fact, FactBlocker,
    DescribeSignalAssignment, FieldValue, GeneratedAssignments, GeneratedEquationSites,
    NormalizedEquation, ProofBudget, SourceSignalAssignment,
};

/// A complete satisfying assignment with a non-Boolean tagged signal.
#[derive(Clone)]
pub(crate) struct BinaryTagCounterexample {
    pub(crate) symbol: SymbolId,
    pub(crate) value: FieldValue,
    pub(crate) constraint_count: usize,
}

struct BinaryTagScope<'a, 'facts> {
    generated: &'a GeneratedEquationSites<'facts>,
    completion: GeneratedAssignments<'a>,
    keys: BTreeSet<AccessKey>,
    witnesses: Vec<(abstract_interpretation::graph::NodeId, NormalizedEquation)>,
    seeds: BTreeMap<AccessKey, FieldValue>,
}

#[derive(Clone, Copy)]
enum TagSeedMode {
    Ordinary,
    ForceTwo,
}

#[derive(Clone, Copy)]
struct ModelSeed {
    input: i32,
    mode: TagSeedMode,
}

#[derive(Default)]
struct SearchState {
    found: BTreeMap<SymbolId, FieldValue>,
    baseline: Option<BTreeMap<AccessKey, FieldValue>>,
}

impl SearchState {
    fn record(
        &mut self,
        facts: &AnalysisFacts<'_>,
        targets: &[AccessKey],
        model: &BTreeMap<AccessKey, FieldValue>,
    ) {
        for target in targets {
            let value = &model[target];
            if !facts.field.is_zero(value) && value != &facts.field.canonical(1.into()) {
                self.found.entry(target.root).or_insert_with(|| value.clone());
            }
        }
    }
}

impl AnalysisFacts<'_> {
    pub(crate) fn local_binary_tag_counterexamples(
        &self,
        symbols: &[SymbolId],
        budget: &mut ProofBudget,
    ) -> Fact<Vec<BinaryTagCounterexample>> {
        match self.binary_tag_results(symbols, budget) {
            Ok(result) => Fact::known(result),
            Err(blockers) => Fact::blocked(blockers),
        }
    }

    fn binary_tag_results(
        &self,
        symbols: &[SymbolId],
        budget: &mut ProofBudget,
    ) -> Result<Vec<BinaryTagCounterexample>, BTreeSet<FactBlocker>> {
        self.preflight_witness_relations()?;
        let readiness = self.body_signal_reads_ready();
        if let Some(blockers) = readiness.unavailable() {
            return Err(blockers.clone());
        }
        let path = self.unique_generation_path(budget)?;
        let mut witness_keys = BTreeSet::new();
        let witnesses = self.all_witness_relations(&path, &mut witness_keys, None)?;
        let generated = self.generated_equation_sites(budget);
        let generated = generated.as_result().map_err(Clone::clone)?;
        checked_generated_path(generated, &path)?;
        let mut keys = generated.keys().clone();
        for key in witness_keys {
            if keys.insert(key) && !budget.reserve_key() {
                return Err(BTreeSet::from([FactBlocker::Budget(self.cfg.exit())]));
            }
        }
        let targets = self.binary_tag_targets(symbols, generated);
        if targets.is_empty() {
            return Ok(Vec::new());
        }
        for target in &targets {
            if keys.insert(target.clone()) && !budget.reserve_key() {
                return Err(BTreeSet::from([FactBlocker::Budget(self.cfg.exit())]));
            }
        }
        self.check_model_keys(&keys)?;
        let completion = self.generated_assignments(generated, budget)?;
        let Some(seeds) = generated_seeds(self.field, generated, budget)? else {
            return Ok(Vec::new());
        };
        BinaryTagScope { generated, completion, keys, witnesses, seeds }
            .search(self, &targets, budget)
    }

    fn preflight_witness_relations(&self) -> Result<(), BTreeSet<FactBlocker>> {
        for id in self.cfg.nodes() {
            let Some(node) = self.cfg.node(*id) else { continue };
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
            if self.witness_relation_for_model(*id)?.is_none() {
                return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(*id)]));
            }
        }
        Ok(())
    }

    fn binary_tag_targets(
        &self,
        symbols: &[SymbolId],
        generated: &GeneratedEquationSites<'_>,
    ) -> Vec<AccessKey> {
        let mut targets = Vec::new();
        let mut equations = BTreeSet::new();
        for site in generated.sites() {
            equations.insert(site.equation());
        }
        for symbol in symbols {
            let target = AccessKey { root: *symbol, instance: None, steps: Vec::new() };
            let expected = boolean_equation(self.field, &target);
            if equations.contains(&expected) {
                continue;
            }
            targets.push(target);
        }
        targets
    }
}

impl BinaryTagScope<'_, '_> {
    fn search(
        &self,
        facts: &AnalysisFacts<'_>,
        targets: &[AccessKey],
        budget: &mut ProofBudget,
    ) -> Result<Vec<BinaryTagCounterexample>, BTreeSet<FactBlocker>> {
        let mut state = SearchState::default();
        for input_seed in [1, 2, 0, -1, 3] {
            for mode in [TagSeedMode::Ordinary, TagSeedMode::ForceTwo] {
                let seed = ModelSeed { input: input_seed, mode };
                let Some(model) = self.candidate(facts, targets, seed, budget)? else {
                    continue;
                };
                if state.baseline.is_none() {
                    state.baseline = Some(model.clone());
                }
                state.record(facts, targets, &model);
                if state.found.len() == targets.len() {
                    return Ok(self.counterexamples(state.found));
                }
            }
        }
        self.vary_inputs(facts, targets, &mut state, budget)?;
        Ok(self.counterexamples(state.found))
    }

    fn candidate(
        &self,
        facts: &AnalysisFacts<'_>,
        targets: &[AccessKey],
        seed: ModelSeed,
        budget: &mut ProofBudget,
    ) -> Result<Option<BTreeMap<AccessKey, FieldValue>>, BTreeSet<FactBlocker>> {
        let mut model = seeded_model(facts, &self.keys, &self.seeds, seed.input);
        if let TagSeedMode::ForceTwo = seed.mode {
            for target in targets {
                model.insert(target.clone(), facts.field.canonical(2.into()));
            }
        }
        self.validate_model(facts, model, budget)
    }

    fn validate_model(
        &self,
        facts: &AnalysisFacts<'_>,
        mut model: BTreeMap<AccessKey, FieldValue>,
        budget: &mut ProofBudget,
    ) -> Result<Option<BTreeMap<AccessKey, FieldValue>>, BTreeSet<FactBlocker>> {
        if !self.completion.complete(facts.field, &mut model, budget)?
            || !witness_relations_hold(facts, &self.witnesses, &model, budget)?
            || !generated_models_satisfy(facts.field, self.generated, &[&model], budget)?
        {
            return Ok(None);
        }
        Ok(Some(model))
    }

    fn vary_inputs(
        &self,
        facts: &AnalysisFacts<'_>,
        targets: &[AccessKey],
        state: &mut SearchState,
        budget: &mut ProofBudget,
    ) -> Result<(), BTreeSet<FactBlocker>> {
        let Some(baseline) = state.baseline.clone() else { return Ok(()) };
        let inputs: BTreeSet<_> = facts
            .hir
            .ports()
            .iter()
            .filter(|port| port.direction == Some(PortDirection::Input))
            .map(|port| port.symbol)
            .collect();
        for key in &self.keys {
            if !inputs.contains(&key.root) {
                continue;
            }
            let mut model = baseline.clone();
            model.insert(key.clone(), facts.field.canonical(2.into()));
            if let Some(model) = self.validate_model(facts, model, budget)? {
                state.record(facts, targets, &model);
            }
            if state.found.len() == targets.len() {
                break;
            }
        }
        Ok(())
    }

    fn counterexamples(
        &self,
        found: BTreeMap<SymbolId, FieldValue>,
    ) -> Vec<BinaryTagCounterexample> {
        found
            .into_iter()
            .map(|(symbol, value)| BinaryTagCounterexample {
                symbol,
                value,
                constraint_count: self.generated.sites().len(),
            })
            .collect()
    }
}

#[cfg(test)]
// Test setup deliberately panics on malformed fixtures.
#[allow(clippy::allow_attributes, clippy::unwrap_used)]
mod tests {
    use std::fs;

    use parser::frontend::{load_sources, Version, VersionPolicy};
    use parser::hir::lift_project;
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::build_cfg;
    use crate::hir_facts::{FactBlocker, ProofBudget};
    use crate::interprocedural::ProjectAnalysis;

    #[test]
    fn binary_tag_batch_refuses_exhausted_budget() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-binary-budget-{}-{:?}",
            std::process::id(),
            std::thread::current().id(),
        ));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(
            &source,
            "pragma circom 2.2.3;template T(){signal output {binary} y;}\
             component main=T();",
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
        let tagged = lifted.hir.symbols().iter().find(|symbol| symbol.name == "y").unwrap();
        let limited = facts
            .local_binary_tag_counterexamples(&[tagged.id], &mut ProofBudget::limited(0, 0, 0, 0));
        assert!(limited.unavailable().is_some());
        let limited_keys = facts.local_binary_tag_counterexamples(
            &[tagged.id],
            &mut ProofBudget::limited(4096, 262_144, 0, 1_048_576),
        );
        assert!(limited_keys
            .unavailable()
            .unwrap()
            .contains(&FactBlocker::Budget(facts.cfg().exit())));
    }
}
