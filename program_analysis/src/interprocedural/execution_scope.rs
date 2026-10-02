//! Shared refusal of warning claims in scopes with a proven execution failure.

use parser::hir::DefinitionRef;

use crate::hir_facts::AnalysisFacts;
use crate::interprocedural::{ContextEvidence, ProjectSummaries, SummaryBlocker};

impl ProjectSummaries<'_> {
    /// Reject a bound definition scope with invalid source or a known failure path.
    ///
    /// Unknown-type regions may remain. Passing this check does not prove
    /// successful completion; rules must certify their own value, reachability,
    /// and dependency predicates. Complete-scope consumers additionally call
    /// `validated_definition`.
    ///
    /// # Errors
    /// Returns the source, provenance, or execution blocker for this scope.
    pub fn check_warning_execution_scope(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.check_call_execution_scope(facts, evidence)?;
        if self.definition_has_hard_source_issue(facts.definition())? {
            return Err(SummaryBlocker::IncompleteDefinition);
        }
        Ok(())
    }

    /// Reject known caller failures without discarding independent facts in partial source.
    pub(super) fn check_call_execution_scope(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.check_facts_for_evidence(facts, evidence)?;
        self.validated_header(facts.definition())?;
        match facts.definition() {
            DefinitionRef::Function(_) => {}
            DefinitionRef::Template(id) => {
                let template = self.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
                if template.custom || template.external {
                    return Err(SummaryBlocker::ExternalSummary);
                }
            }
            DefinitionRef::Bus(_) => return Err(SummaryBlocker::UnsupportedContext),
        }
        if self.template_definitely_fails(facts)? {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        Ok(())
    }
}
