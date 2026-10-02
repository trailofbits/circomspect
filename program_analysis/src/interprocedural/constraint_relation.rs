//! Provider-bound generated equation evidence for validated template scopes.

use abstract_interpretation::graph::NodeId;

use crate::hir_facts::{AnalysisFacts, GeneratedEquation};
use crate::interprocedural::{ContextEvidence, ProjectSummaries, SummaryBlocker, SummaryFact};
use crate::interprocedural::summary::certified;

impl ProjectSummaries<'_> {
    /// Certify a generated equation equivalent to an exact witness write.
    ///
    /// The certificate requires a validated root template scope, complete
    /// analysis, and no known execution failure. Called templates abstain
    /// until incoming constraint closure is known.
    pub fn template_generated_equation(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        witness: NodeId,
    ) -> SummaryFact<Option<GeneratedEquation>> {
        SummaryFact::from_result(self.generated_equation(facts, evidence, witness))
    }

    fn generated_equation(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        witness: NodeId,
    ) -> Result<Option<GeneratedEquation>, SummaryBlocker> {
        self.check_template_constraint_scope(facts, evidence)?;
        Ok(certified(&facts.must_equation_for_witness(witness))?.clone())
    }
}
