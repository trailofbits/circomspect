//! Provider-bound generated equation evidence for validated template scopes.

use abstract_interpretation::graph::NodeId;

use parser::hir::{AccessPath, SymbolId};

use crate::hir_facts::{
    AnalysisFacts, BinaryTagCounterexample, FeasibleZeroDivisor, GeneratedEquation, ProofBudget,
    WitnessAlternative,
};
use crate::interprocedural::{ContextEvidence, TemplateQueries, SummaryBlocker, SummaryFact};
use crate::interprocedural::summary::certified;

/// Equation queries tied to one immutable fact snapshot and its checked scope.
///
/// The provider validates the shared scope once. Every query still checks its
/// own witness node, generated equation, and dependency closure. Failed scope
/// validation is retained for every query and cannot expose provisional facts.
///
/// This query object borrows the supplied facts and carries the checked template-scope
/// refusal state. It is not an eager certificate for every equation: each operation can still
/// be unavailable and must retain its originating context checks.
pub struct GeneratedEquationQueries<'facts, 'project> {
    facts: &'facts AnalysisFacts<'project>,
    scope: Result<(), SummaryBlocker>,
}

impl GeneratedEquationQueries<'_, '_> {
    /// Certify an equivalent generated equation for this snapshot's witness node.
    #[must_use]
    pub fn for_witness(&self, witness: NodeId) -> SummaryFact<Option<GeneratedEquation>> {
        let result = self
            .scope
            .clone()
            .and_then(|()| Ok(certified(&self.facts.must_equation_for_witness(witness))?.clone()));
        SummaryFact::from_result(result)
    }

    /// Search two complete models for a witness-only assignment in this root scope.
    pub(crate) fn witness_alternative(
        &self,
        witness: NodeId,
    ) -> SummaryFact<Option<WitnessAlternative>> {
        let result = self.scope.clone().and_then(|()| {
            let fact = self.facts.local_witness_alternative(witness, &mut ProofBudget::default());
            certified(&fact).cloned()
        });
        SummaryFact::from_result(result)
    }

    pub(crate) fn feasible_zero_divisor(
        &self,
        witness: NodeId,
        divisor: &AccessPath,
    ) -> SummaryFact<Option<FeasibleZeroDivisor>> {
        let result = self.scope.clone().and_then(|()| {
            let fact = self.facts.local_feasible_zero_divisor(
                witness,
                divisor,
                &mut ProofBudget::default(),
            );
            certified(&fact).cloned()
        });
        SummaryFact::from_result(result)
    }

    pub(crate) fn binary_tag_counterexamples(
        &self,
        symbols: &[SymbolId],
    ) -> SummaryFact<Vec<BinaryTagCounterexample>> {
        let result = self.scope.clone().and_then(|()| {
            let fact =
                self.facts.local_binary_tag_counterexamples(symbols, &mut ProofBudget::default());
            certified(&fact).cloned()
        });
        SummaryFact::from_result(result)
    }
}

impl TemplateQueries<'_, '_> {
    /// Validate a root template scope for a batch of generated equation queries.
    ///
    /// Each batch borrows one exact fact snapshot. Complete solving and no known
    /// execution failure are required; called templates without incoming
    /// constraint closure retain an unavailable result for every query.
    #[must_use]
    pub fn template_generated_equations<'facts, 'project>(
        &self,
        facts: &'facts AnalysisFacts<'project>,
        evidence: &ContextEvidence,
    ) -> GeneratedEquationQueries<'facts, 'project> {
        GeneratedEquationQueries {
            facts,
            scope: self.check_template_constraint_scope(facts, evidence),
        }
    }
}

#[cfg(test)]
mod tests;
