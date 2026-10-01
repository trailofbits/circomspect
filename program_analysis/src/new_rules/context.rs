use parser::hir::{DefinitionRef, HirProject, PortId};
use parser::new_frontend::Span;

use crate::hir_facts::AnalysisFacts;
use crate::interprocedural::{
    CallContext, ContextEvidence, FunctionEffects, FunctionSummary, PortSummary, ProjectSummaries,
    SummaryBlocker, SummaryFact, WitnessSite,
};

use crate::new_rules::{Finding, RuleKind};

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
///
/// ```compile_fail
/// use circomspect_program_analysis::new_rules::RuleContext;
/// fn bypass(context: &RuleContext<'_, '_, '_>) {
///     let _ = context.summaries().context_for(context.call_context().definition(), vec![]);
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
    pub fn call_context(&self) -> &CallContext {
        self.evidence.context()
    }

    #[must_use]
    pub fn origin(&self) -> crate::interprocedural::ContextOrigin {
        self.evidence.origin()
    }

    /// Return a summary only for the active function specialization.
    #[must_use]
    pub fn function_summary(&self) -> Option<SummaryFact<FunctionSummary>> {
        let DefinitionRef::Function(id) = self.call_context().definition() else { return None };
        Some(self.summaries.function(id, self.call_context()))
    }

    /// Return effects only for the active function specialization.
    #[must_use]
    pub fn function_effects(&self) -> Option<SummaryFact<FunctionEffects>> {
        let DefinitionRef::Function(id) = self.call_context().definition() else { return None };
        Some(self.summaries.function_effects(id, self.call_context()))
    }

    /// Return generated-constraint facts for an active template's declared port element.
    #[must_use]
    pub fn template_port(
        &self,
        port: PortId,
        indices: &[usize],
    ) -> Option<SummaryFact<PortSummary>> {
        let DefinitionRef::Template(id) = self.call_context().definition() else { return None };
        Some(self.summaries.template_port_at(id, self.call_context(), port, indices))
    }

    /// Return whether the active template reads a declared port.
    #[must_use]
    pub fn template_port_read(&self, port: PortId) -> Option<SummaryFact<bool>> {
        let DefinitionRef::Template(id) = self.call_context().definition() else { return None };
        Some(self.summaries.template_port_read(id, self.call_context(), port))
    }

    /// Return witness writes to a declared port in the active template.
    #[must_use]
    pub fn template_port_witnesses(&self, port: PortId) -> Option<SummaryFact<Vec<WitnessSite>>> {
        let DefinitionRef::Template(id) = self.call_context().definition() else { return None };
        Some(self.summaries.template_port_witnesses(id, self.call_context(), port))
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
