//! Provider-bound bit relations in validated template scopes.

use parser::hir::AccessPath;

use crate::hir_facts::{
    AccessHandle, AnalysisFacts, BitAmbiguityOutcome, BitDecomposition, ProofBudget,
};
use crate::interprocedural::summary::certified;
use crate::interprocedural::{
    ContextEvidence, ContextOrigin, SummaryBlocker, SummaryFact, TemplateQueries,
};

impl TemplateQueries<'_, '_> {
    /// Prove two complete models of a validated leaf template's generated equations.
    ///
    /// The bounded candidates share every external input. Unknown control, called
    /// scopes and symbolic template parameters withhold this existential proof.
    pub fn template_bit_ambiguity(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        input: &AccessPath,
        bits: &[AccessPath],
    ) -> SummaryFact<BitAmbiguityOutcome> {
        let result = self.check_bit_ambiguity_scope(facts, evidence).and_then(|()| {
            let fact = facts.local_bit_ambiguity(input, bits, &mut ProofBudget::default());
            certified(&fact).cloned()
        });
        SummaryFact::from_result(result)
    }

    /// Prove two complete models using exact, context-bound local ports.
    ///
    /// This checks the same generated equations and caller scope as the path
    /// query while allowing concrete array elements in a specialized loop.
    pub fn template_bit_ambiguity_handles(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        input: &AccessHandle,
        bits: &[AccessHandle],
    ) -> SummaryFact<BitAmbiguityOutcome> {
        let result = self.check_bit_ambiguity_scope(facts, evidence).and_then(|()| {
            let fact = facts.local_bit_ambiguity_handles(input, bits, &mut ProofBudget::default());
            certified(&fact).cloned()
        });
        SummaryFact::from_result(result)
    }

    fn check_bit_ambiguity_scope(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.check_template_constraint_scope(facts, evidence)?;
        if evidence.origin() == ContextOrigin::SymbolicRoot
            && !evidence.context().arguments().is_empty()
        {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        Ok(())
    }

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

    /// Certify a local relation for exact, context-bound template ports.
    ///
    /// This proves generated body equations in a validated root scope. An
    /// accepted input domain and two satisfying models require separate proof.
    pub fn template_bit_decomposition_handles(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        input: &AccessHandle,
        bits: &[AccessHandle],
    ) -> SummaryFact<Option<BitDecomposition>> {
        let result = self
            .check_template_constraint_scope(facts, evidence)
            .and_then(|()| Ok(certified(&facts.bit_decomposition_handles(input, bits))?.clone()));
        SummaryFact::from_result(result)
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
