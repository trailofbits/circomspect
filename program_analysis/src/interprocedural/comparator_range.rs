//! Generated comparator relations in a complete main/comparator/decomposition closure.

mod model;
mod pattern;
mod source;

use std::collections::BTreeSet;

use abstract_interpretation::graph::NodeId;
use num_bigint::BigInt;
use parser::new_frontend::Span;

use crate::hir_cfg::Origin;
use crate::hir_facts::{
    AccessKey, AnalysisFacts, BitDecomposition, FieldValue, GeneratedEquationSites, ProofBudget,
};
use crate::interprocedural::comparator_range::model::validate_candidate;
use crate::interprocedural::comparator_range::pattern::ComparatorPattern;
use crate::interprocedural::input_relation::ReadyGeneratedInputs;
use crate::interprocedural::summary::certified;
use crate::interprocedural::{AppliedComponentPort, ProjectSummaries, SummaryBlocker, SummaryFact};

/// A generated-fixed comparator input outside the proved integer comparison range.
///
/// The provider also checked one complete satisfying model of every generated
/// equation in all three scopes. This makes no witness-execution or exploit claim.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ComparatorRangeViolation {
    applied: AppliedComponentPort,
    decomposition: BitDecomposition,
    input: AccessKey,
    value: FieldValue,
    bound: BigInt,
    span: Span,
    origins: Vec<Origin>,
}

impl ComparatorRangeViolation {
    #[must_use]
    pub fn applied_port(&self) -> &AppliedComponentPort {
        &self.applied
    }
    #[must_use]
    pub fn decomposition(&self) -> &BitDecomposition {
        &self.decomposition
    }
    #[must_use]
    pub fn input(&self) -> &AccessKey {
        &self.input
    }
    #[must_use]
    pub fn value(&self) -> &FieldValue {
        &self.value
    }
    #[must_use]
    pub fn upper_bound(&self) -> &BigInt {
        &self.bound
    }
    #[must_use]
    pub const fn binding_span(&self) -> Span {
        self.span
    }
    #[must_use]
    pub fn constraint_origins(&self) -> &[Origin] {
        &self.origins
    }
}

struct ComparatorScope<'a> {
    facts: &'a AnalysisFacts<'a>,
    sites: &'a GeneratedEquationSites<'a>,
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

struct ComparatorClosure<'a> {
    main: ComparatorScope<'a>,
    comparison: ComparatorScope<'a>,
    decomposition: ComparatorScope<'a>,
    main_ready: &'a ReadyGeneratedInputs,
    comparison_ready: &'a ReadyGeneratedInputs,
    pattern: ComparatorPattern,
}

impl ProjectSummaries<'_> {
    /// Prove generated-fixed inputs outside a generated comparator's safe range.
    ///
    /// The applied output must belong to the sole comparator under this exact
    /// main. One nested leaf must prove ordered Boolean reconstruction. Unknown
    /// source/control or missing bindings withhold evidence. An empty result means
    /// no range-violation certificate; it never proves safe inputs or unsatisfiability.
    pub fn component_comparator_range(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
    ) -> SummaryFact<Vec<ComparatorRangeViolation>> {
        SummaryFact::from_result(self.comparator_range_result(
            facts,
            applied,
            &mut ProofBudget::default(),
        ))
    }

    fn comparator_range_result(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
        budget: &mut ProofBudget,
    ) -> Result<Vec<ComparatorRangeViolation>, SummaryBlocker> {
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
                    return Ok(Vec::new());
                };
                let closure = ComparatorClosure {
                    main,
                    comparison,
                    decomposition,
                    main_ready: &main_ready,
                    comparison_ready: &ready,
                    pattern,
                };
                validate_candidate(self.field_context(), applied, &closure, budget)
            })
        })
    }
}

#[cfg(test)]
mod tests;
