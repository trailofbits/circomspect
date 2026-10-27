//! The checked three-scope closure is issued only after every source and generation check.

mod model;

#[cfg(test)]
mod tests;

use std::collections::BTreeSet;

use abstract_interpretation::graph::NodeId;

use crate::hir_facts::{AnalysisFacts, Fact, FieldContext, GeneratedEquationSites, ProofBudget};
use crate::interprocedural::comparator_range::{ComparatorQuery, ComparatorRangeViolation};
use crate::interprocedural::comparator_range::pattern::ComparatorPattern;
use crate::interprocedural::input_relation::ReadyGeneratedInputs;
use crate::interprocedural::output_enumeration::EnumeratedComponentInstance;
use crate::interprocedural::summary::certified;
use crate::interprocedural::{AppliedComponentPort, SummaryBlocker, ValidatedConstructorReads};

pub(super) struct ComparatorScope<'a> {
    pub(super) facts: &'a AnalysisFacts<'a>,
    pub(super) sites: &'a GeneratedEquationSites<'a>,
}

impl ComparatorScope<'_> {
    fn check(
        &self,
        path: &BTreeSet<NodeId>,
        ready: Option<&ReadyGeneratedInputs>,
    ) -> Result<(), SummaryBlocker> {
        let mut local = BTreeSet::new();
        for key in self.sites.keys() {
            let bound = ready.is_some_and(|ready| ready.ports().contains_access(key));
            if !bound {
                local.insert(key.clone());
            }
        }
        self.facts.check_model_keys(&local).map_err(SummaryBlocker::LocalFacts)?;
        if self.sites.sites().iter().any(|site| !path.contains(&site.site())) {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        Ok(())
    }
}

/// A complete generated closure bound to the output and field that were checked.
/// The borrowed facts and equations cannot outlive the construction callback.
///
/// The closure issuer checks main, comparison, and decomposition scopes, paths, readiness,
/// and recognized relation before invoking the callback. Its borrowed field, facts, equations,
/// and ready inputs stay inside that callback. A range violation is issued only after a
/// candidate satisfies every participating equation.
pub(super) struct CheckedComparatorClosure<'a> {
    field: &'a FieldContext,
    applied: &'a AppliedComponentPort,
    main: ComparatorScope<'a>,
    comparison: ComparatorScope<'a>,
    decomposition: ComparatorScope<'a>,
    main_ready: &'a ReadyGeneratedInputs,
    comparison_ready: &'a ReadyGeneratedInputs,
    pattern: ComparatorPattern,
}

impl CheckedComparatorClosure<'_> {
    pub(super) fn validate_candidate(
        &self,
        budget: &mut ProofBudget,
    ) -> Result<Vec<ComparatorRangeViolation>, SummaryBlocker> {
        model::validate_candidate(self, budget)
    }
}

struct ComparatorStage<'scope> {
    comparison: &'scope AnalysisFacts<'scope>,
    decomposition: &'scope AnalysisFacts<'scope>,
    comparison_instance: &'scope EnumeratedComponentInstance,
    decomposition_instance: &'scope EnumeratedComponentInstance,
    main_ready: &'scope ReadyGeneratedInputs,
    comparison_ready: &'scope ReadyGeneratedInputs,
}

struct ComparatorObservations<'scope> {
    paths: [Result<BTreeSet<NodeId>, SummaryBlocker>; 3],
    sites: [Fact<GeneratedEquationSites<'scope>>; 3],
}

impl<'query, 'hir: 'query> ComparatorQuery<'query, 'hir> {
    pub(super) fn with_checked_closure<T, F>(
        &self,
        budget: &mut ProofBudget,
        work: F,
    ) -> Result<Option<T>, SummaryBlocker>
    where
        F: FnOnce(&CheckedComparatorClosure<'_>, &mut ProofBudget) -> Result<T, SummaryBlocker>,
    {
        let analysis = self.analysis;
        let facts = self.facts;
        let applied = self.applied;
        self.check_output()?;
        analysis.check_parent_components_complete(facts)?;
        analysis.single_model_call(facts, applied)?;
        analysis.components().with_component_port_facts(applied.callee_evidence(), |comparison| {
            let instance = analysis.model_source_instance(facts, comparison, applied, budget)?;
            let main_ready = analysis
                .components()
                .ready_generated_instance(facts, comparison, &instance, budget)?;
            let nested = self.comparator_child(comparison, &instance.callee)?;
            analysis.components().with_component_port_facts(&nested.callee, |decomposition| {
                let ready = analysis.components().ready_generated_instance(
                    comparison,
                    decomposition,
                    &nested,
                    budget,
                )?;
                let stage = ComparatorStage {
                    comparison,
                    decomposition,
                    comparison_instance: &instance,
                    decomposition_instance: &nested,
                    main_ready: &main_ready,
                    comparison_ready: &ready,
                };
                let (constructors, parent_constructors) = self.check_generation(&stage)?;
                let observations =
                    self.observe_generation(&stage, &constructors, &parent_constructors, budget);
                let [main_path, comparison_path, decomposition_path] = observations.paths;
                let [main_sites, comparison_sites, decomposition_sites] = observations.sites;
                let scopes = [
                    ComparatorScope { facts, sites: certified(&main_sites)? },
                    ComparatorScope { facts: comparison, sites: certified(&comparison_sites)? },
                    ComparatorScope {
                        facts: decomposition,
                        sites: certified(&decomposition_sites)?,
                    },
                ];
                let [main, comparison, decomposition] = scopes;
                main.check(&main_path?, Some(&main_ready))?;
                comparison.check(&comparison_path?, Some(&ready))?;
                decomposition.check(&decomposition_path?, None)?;
                let Some(pattern) = ComparatorPattern::find(
                    analysis.field_context(),
                    applied,
                    [&comparison, &decomposition],
                    &ready,
                    budget,
                )?
                else {
                    return Ok(None);
                };
                let closure = CheckedComparatorClosure {
                    field: analysis.field_context(),
                    applied,
                    main,
                    comparison,
                    decomposition,
                    main_ready: &main_ready,
                    comparison_ready: &ready,
                    pattern,
                };
                work(&closure, budget).map(Some)
            })
        })
    }

    fn check_generation(
        &self,
        stage: &ComparatorStage<'_>,
    ) -> Result<(ValidatedConstructorReads, ValidatedConstructorReads), SummaryBlocker> {
        let execution = self.analysis.execution();
        let completed = execution.completed_project_template(
            stage.decomposition,
            &stage.decomposition_instance.callee,
            &[],
        )?;
        let children = [execution.completed_generated_child(
            stage.comparison,
            stage.decomposition_instance,
            completed,
            stage.comparison_ready,
        )?];
        let constructors = execution.completed_constructor_reads(
            stage.comparison,
            &stage.comparison_instance.callee,
            &children,
        )?;
        let completed = execution.completed_generated_template(
            stage.comparison,
            &children,
            stage.comparison_ready,
        )?;
        let children = [execution.completed_generated_child(
            self.facts,
            stage.comparison_instance,
            completed,
            stage.main_ready,
        )?];
        let parent_constructors = execution.completed_constructor_reads(
            self.facts,
            self.applied.caller_evidence(),
            &children,
        )?;
        let completed =
            execution.completed_generated_template(self.facts, &children, stage.main_ready)?;
        self.analysis.check_completed_model_main(
            self.facts,
            self.applied.caller_evidence(),
            &completed,
        )?;
        Ok((constructors, parent_constructors))
    }

    fn observe_generation<'scope>(
        &self,
        stage: &ComparatorStage<'scope>,
        comparison_constructors: &ValidatedConstructorReads,
        parent_constructors: &ValidatedConstructorReads,
        budget: &mut ProofBudget,
    ) -> ComparatorObservations<'scope>
    where
        'query: 'scope,
    {
        let facts: &'scope AnalysisFacts<'scope> = self.facts;
        let paths = [
            facts.unique_generation_path_with(budget, parent_constructors),
            stage.comparison.unique_generation_path_with(budget, comparison_constructors),
            stage.decomposition.unique_generation_path(budget),
        ];
        let paths = paths.map(|path| path.map_err(SummaryBlocker::LocalFacts));
        let sites = [
            facts.generated_component_equation_sites(budget, stage.main_ready.ports()),
            stage
                .comparison
                .generated_component_equation_sites(budget, stage.comparison_ready.ports()),
            stage.decomposition.generated_equation_sites(budget),
        ];
        ComparatorObservations { paths, sites }
    }
}
