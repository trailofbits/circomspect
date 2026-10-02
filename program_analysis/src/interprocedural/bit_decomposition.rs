//! Provider-bound bit relations in validated template scopes.

use parser::hir::AccessPath;

use crate::hir_facts::{AnalysisFacts, BitDecomposition};
use crate::interprocedural::summary::certified;
use crate::interprocedural::{ContextEvidence, ProjectSummaries, SummaryBlocker, SummaryFact};

impl ProjectSummaries<'_> {
    /// Certify a local bit relation in a validated root template scope.
    ///
    /// This does not establish an accepted input domain or two satisfying bit
    /// vectors. Called scopes abstain until their caller constraint closure is
    /// proved.
    pub fn template_bit_decomposition(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        input: &AccessPath,
        bits: &[AccessPath],
    ) -> SummaryFact<Option<BitDecomposition>> {
        SummaryFact::from_result(self.validated_bit_decomposition(facts, evidence, input, bits))
    }

    fn validated_bit_decomposition(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        input: &AccessPath,
        bits: &[AccessPath],
    ) -> Result<Option<BitDecomposition>, SummaryBlocker> {
        self.check_template_constraint_scope(facts, evidence)?;
        Ok(certified(&facts.bit_decomposition(input, bits))?.clone())
    }
}
