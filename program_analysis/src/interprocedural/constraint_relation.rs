//! Provider-bound generated equation evidence for validated template scopes.

use abstract_interpretation::graph::NodeId;

use crate::hir_facts::{AnalysisFacts, GeneratedEquation};
use crate::interprocedural::{ContextEvidence, ProjectSummaries, SummaryBlocker, SummaryFact};
use crate::interprocedural::summary::certified;

/// Equation queries tied to one immutable fact snapshot and its checked scope.
///
/// The provider validates the shared scope once. Every query still checks its
/// own witness node, generated equation, and dependency closure. Failed scope
/// validation is retained for every query and cannot expose provisional facts.
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
}

impl ProjectSummaries<'_> {
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
