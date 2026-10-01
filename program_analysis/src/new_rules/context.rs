use parser::hir::HirProject;
use parser::new_frontend::Span;

use crate::hir_facts::AnalysisFacts;
use crate::interprocedural::{CallContext, ContextEvidence, ProjectSummaries, SummaryBlocker};

use super::{Finding, RuleKind};

/// Validated local facts and summary scope for one definition and selected curve.
/// A hypothetical specialization key cannot authorize a rule run.
///
/// ```compile_fail
/// use circomspect_program_analysis::hir_facts::AnalysisFacts;
/// use circomspect_program_analysis::interprocedural::{CallContext, ProjectSummaries};
/// use circomspect_program_analysis::new_rules::RuleContext;
/// fn bypass(
///     facts: &AnalysisFacts<'_>,
///     summaries: &ProjectSummaries<'_>,
///     hypothetical: &CallContext,
/// ) {
///     let _ = RuleContext::new(facts, summaries, hypothetical);
/// }
/// ```
pub struct RuleContext<'a, 'facts, 'project> {
    facts: &'a AnalysisFacts<'facts>,
    summaries: &'a ProjectSummaries<'project>,
    evidence: &'a ContextEvidence,
}

impl<'a, 'facts, 'project> RuleContext<'a, 'facts, 'project> {
    /// Pair a checked local analysis with a provider-issued root or reachable call.
    pub fn new(
        facts: &'a AnalysisFacts<'facts>,
        summaries: &'a ProjectSummaries<'project>,
        evidence: &'a ContextEvidence,
    ) -> Result<Self, RuleContextError> {
        if facts.hir().identity() != summaries.hir().identity() {
            return Err(RuleContextError::ForeignProject);
        }
        if facts.curve() != summaries.curve() {
            return Err(RuleContextError::WrongCurve);
        }
        summaries.check_evidence(evidence).map_err(RuleContextError::InvalidEvidence)?;
        if facts.definition() != evidence.context().definition() {
            return Err(RuleContextError::WrongDefinition);
        }
        summaries
            .check_facts_for_evidence(facts, evidence)
            .map_err(RuleContextError::MismatchedFacts)?;
        Ok(Self { facts, summaries, evidence })
    }

    #[must_use]
    pub fn hir(&self) -> &HirProject {
        self.facts.hir()
    }

    #[must_use]
    pub fn facts(&self) -> &AnalysisFacts<'facts> {
        self.facts
    }

    #[must_use]
    pub fn summaries(&self) -> &ProjectSummaries<'project> {
        self.summaries
    }

    #[must_use]
    pub fn call_context(&self) -> &CallContext {
        self.evidence.context()
    }

    #[must_use]
    pub fn origin(&self) -> crate::interprocedural::ContextOrigin {
        self.evidence.origin()
    }

    /// Create a finding in this validated scope after the rule proves its predicate.
    #[must_use]
    pub fn finding(
        &self,
        kind: RuleKind,
        message: String,
        primary: Span,
        primary_label: String,
    ) -> Finding {
        Finding::at(self.call_context().clone(), kind, message, primary, primary_label)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub enum RuleContextError {
    #[error("local facts and summaries come from different HIR projects")]
    ForeignProject,
    #[error("local facts and summaries use different Circom field curves")]
    WrongCurve,
    #[error("local facts and summary evidence refer to different definitions")]
    WrongDefinition,
    #[error("summary evidence is invalid for this project: {0:?}")]
    InvalidEvidence(SummaryBlocker),
    #[error("local facts were not computed for the summary evidence context: {0:?}")]
    MismatchedFacts(SummaryBlocker),
}
