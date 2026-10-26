//! Generated comparator relations in a complete main/comparator/decomposition closure.

mod closure;
mod pattern;
mod source;

use num_bigint::BigInt;
use parser::frontend::Span;

use crate::hir_cfg::Origin;
use crate::hir_facts::{AccessKey, AnalysisFacts, BitDecomposition, FieldValue, ProofBudget};
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
        let result =
            self.with_checked_comparator_closure(facts, applied, budget, |closure, budget| {
                closure.validate_candidate(budget)
            })?;
        Ok(result.unwrap_or_default())
    }
}

#[cfg(test)]
mod tests;
