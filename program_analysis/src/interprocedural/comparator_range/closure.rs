//! The checked three-scope closure is issued only after every source and generation check.

mod model;

use std::collections::BTreeSet;

use abstract_interpretation::graph::NodeId;

use crate::hir_facts::{AnalysisFacts, FieldContext, GeneratedEquationSites, ProofBudget};
use crate::interprocedural::comparator_range::ComparatorRangeViolation;
use crate::interprocedural::comparator_range::pattern::ComparatorPattern;
use crate::interprocedural::input_relation::ReadyGeneratedInputs;
use crate::interprocedural::summary::certified;
use crate::interprocedural::{AppliedComponentPort, ProjectAnalysis, SummaryBlocker};

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

impl ProjectAnalysis<'_> {
    pub(super) fn with_checked_comparator_closure<T, F>(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
        budget: &mut ProofBudget,
        work: F,
    ) -> Result<Option<T>, SummaryBlocker>
    where
        F: FnOnce(&CheckedComparatorClosure<'_>, &mut ProofBudget) -> Result<T, SummaryBlocker>,
    {
        self.check_comparator_output(facts, applied)?;
        self.check_parent_components_complete(facts)?;
        self.single_model_call(facts, applied)?;
        self.with_component_port_facts(applied.callee_evidence(), |comparison| {
            let instance = self.model_source_instance(facts, comparison, applied, budget)?;
            let main_ready = self.ready_generated_instance(facts, comparison, &instance, budget)?;
            let nested = self.comparator_child(comparison, &instance.callee)?;
            self.with_component_port_facts(&nested.callee, |decomposition| {
                let ready =
                    self.ready_generated_instance(comparison, decomposition, &nested, budget)?;
                let completed =
                    self.completed_project_template(decomposition, &nested.callee, &[])?;
                let children =
                    [self.completed_generated_child(comparison, &nested, completed, &ready)?];
                let constructors =
                    self.completed_constructor_reads(comparison, &instance.callee, &children)?;
                let completed = self.completed_generated_template(comparison, &children, &ready)?;
                let children =
                    [self.completed_generated_child(facts, &instance, completed, &main_ready)?];
                let parent_constructors =
                    self.completed_constructor_reads(facts, applied.caller_evidence(), &children)?;
                let completed = self.completed_generated_template(facts, &children, &main_ready)?;
                self.check_completed_model_main(facts, applied.caller_evidence(), &completed)?;
                let paths = [
                    facts.unique_generation_path_with(budget, &parent_constructors),
                    comparison.unique_generation_path_with(budget, &constructors),
                    decomposition.unique_generation_path(budget),
                ];
                let [main_path, comparison_path, decomposition_path] =
                    paths.map(|path| path.map_err(SummaryBlocker::LocalFacts));
                let main_sites =
                    facts.generated_component_equation_sites(budget, main_ready.ports());
                let comparison_sites =
                    comparison.generated_component_equation_sites(budget, ready.ports());
                let decomposition_sites = decomposition.generated_equation_sites(budget);
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
                    self.field_context(),
                    applied,
                    [&comparison, &decomposition],
                    &ready,
                    budget,
                )?
                else {
                    return Ok(None);
                };
                let closure = CheckedComparatorClosure {
                    field: self.field_context(),
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
}
