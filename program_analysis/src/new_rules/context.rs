use parser::hir::{AccessPath, DefinitionRef, HirProject, PortId};
use parser::frontend::Span;

use crate::hir_facts::{
    AccessHandle, AnalysisFacts, AssignmentDemand, BitAmbiguityOutcome, BitDecomposition, Fact,
};
use crate::interprocedural::{
    AppliedComponentPort, CallBlocker, CallContext, CallOwner, CallReachability, CallSite,
    CallPathSite, CallSiteId, CallerOutputRead, ComposedConstraintFixedOutput, ContextEvidence,
    ComponentBitAmbiguityOutcome, EnumeratedComponentOutput, FunctionEffects, FunctionSummary,
    GeneratedEquationQueries, PortSummary, ProjectOutputUse, ProjectSummaries, SummaryBlocker,
    SummaryFact, ValidatedDefinition, ValidatedHeader, WitnessSite,
};

use crate::new_rules::{AbstentionReason, Finding, RuleKind, ScopedAbstention};

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
    ///
    /// # Errors
    /// Returns an error for foreign facts, a different field or definition, or invalid evidence.
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

    /// Validate this active function or template's header and parameter list.
    ///
    /// # Errors
    /// Returns a blocker when source recovery or validation prevents a complete header proof.
    pub fn validated_header(&self) -> Result<ValidatedHeader, SummaryBlocker> {
        self.summaries.validated_header(self.call_context().definition())
    }

    /// Validate source recovery across this active definition's body and header.
    ///
    /// # Errors
    /// Returns a blocker when source recovery leaves the active definition incomplete.
    pub fn validated_definition(&self) -> Result<ValidatedDefinition, SummaryBlocker> {
        self.summaries.validated_definition(self.facts)
    }

    /// Refuse claims in an active scope with a known execution failure path.
    ///
    /// Passing this check does not prove that the definition completes.
    ///
    /// # Errors
    /// Returns a blocker for an invalid source scope or a proved execution failure.
    pub fn check_warning_execution_scope(&self) -> Result<(), SummaryBlocker> {
        self.summaries.check_warning_execution_scope(self.facts, self.evidence)
    }

    /// Prove observable demand for a source-matched scalar assignment.
    ///
    /// Both complete source coverage and the known-failure refusal precede
    /// local demand certification. The returned fact retains solver blockers.
    ///
    /// # Errors
    /// Returns a blocker when source completeness or execution validity cannot be established.
    pub fn assignment_demand(
        &self,
        node: abstract_interpretation::graph::NodeId,
        target: &parser::hir::AccessPath,
    ) -> Result<Fact<AssignmentDemand>, SummaryBlocker> {
        self.validated_definition()?;
        self.check_warning_execution_scope()?;
        Ok(self.facts.assignment_demand(node, target, self.evidence))
    }

    #[must_use]
    pub fn origin(&self) -> crate::interprocedural::ContextOrigin {
        self.evidence.origin()
    }

    /// Provider-issued source calls from a main or symbolic root to this scope.
    #[must_use]
    pub fn call_path(&self) -> &[CallPathSite] {
        self.evidence.call_path()
    }

    /// The exact source call that invoked this scope, if it has one.
    #[must_use]
    pub fn incoming_call_site(&self) -> Option<&CallPathSite> {
        self.call_path().last()
    }

    /// List call sites owned by the active definition, including unresolved sites.
    #[must_use]
    pub fn call_sites(&self) -> Vec<&CallSite> {
        self.summaries.graph().calls_from(CallOwner::Definition(self.call_context().definition()))
    }

    /// Bind a child-local output summary to one may-reachable exact component instance.
    ///
    /// This does not certify caller-side constraint relations, witness readiness, or output use.
    ///
    /// # Errors
    /// Returns a call blocker when reachability cannot be certified.
    pub fn applied_component_port(
        &self,
        site: CallSiteId,
        handle: &AccessHandle,
    ) -> Result<Option<SummaryFact<AppliedComponentPort>>, CallBlocker> {
        match self.summaries.graph().reachable_call(site, self.facts) {
            CallReachability::Reachable(call) => Ok(Some(self.summaries.apply_component_output(
                self.facts,
                self.evidence,
                &call,
                handle,
            ))),
            CallReachability::Unreachable => Ok(None),
            CallReachability::Unavailable(blocker) => Err(blocker),
        }
    }

    /// Bind a reachable child array output through its own checked first element.
    ///
    /// The child port dimension is proved under the callee's exact parameters.
    /// A source call that is unreachable returns `None`; unresolved reachability
    /// retains its typed blocker.
    ///
    /// # Errors
    /// Returns a call blocker when reachability cannot be certified.
    pub fn applied_component_first_output(
        &self,
        site: CallSiteId,
        output: PortId,
    ) -> Result<Option<SummaryFact<AppliedComponentPort>>, CallBlocker> {
        match self.summaries.graph().reachable_call(site, self.facts) {
            CallReachability::Reachable(call) => {
                Ok(Some(self.summaries.apply_component_first_output(
                    self.facts,
                    self.evidence,
                    &call,
                    output,
                )))
            }
            CallReachability::Unreachable => Ok(None),
            CallReachability::Unavailable(blocker) => Err(blocker),
        }
    }

    /// Prove a caller-side fixed output from a child equality and checked input binding.
    ///
    /// The applied port must belong to this exact source scope. The result proves a
    /// constraint relation; it does not by itself prove an output witness write.
    ///
    /// # Errors
    /// Returns a blocker when the applied port belongs to another caller scope.
    pub fn composed_constraint_fixed_output(
        &self,
        applied: &AppliedComponentPort,
    ) -> Result<SummaryFact<ComposedConstraintFixedOutput>, SummaryBlocker> {
        if applied.caller_evidence() != self.evidence {
            return Err(SummaryBlocker::WrongContext);
        }
        Ok(self.summaries.composed_constraint_fixed_output(self.facts, applied))
    }

    /// Prove an exact output read in this caller's reachable body.
    ///
    /// No local read returns unavailable evidence. It cannot prove that the
    /// output is unused across the project or in an uninstantiated library.
    ///
    /// # Errors
    /// Returns a blocker when the applied port belongs to another caller scope.
    pub fn caller_output_read(
        &self,
        applied: &AppliedComponentPort,
    ) -> Result<SummaryFact<CallerOutputRead>, SummaryBlocker> {
        if applied.caller_evidence() != self.evidence {
            return Err(SummaryBlocker::WrongContext);
        }
        Ok(self.summaries.caller_output_read(self.facts, applied))
    }

    /// Certify output use across every exact instance path below the active main.
    ///
    /// An incomplete project or uninstantiated library root returns unavailable
    /// evidence. Positive local reads remain available independently.
    #[must_use]
    pub fn closed_project_output_uses(&self) -> SummaryFact<Vec<ProjectOutputUse>> {
        self.summaries.closed_project_output_uses(self.facts, self.evidence)
    }

    /// Prove incidence for an exact internal signal in this validated root template.
    #[must_use]
    pub fn template_internal_signal_incidence(
        &self,
        path: &parser::hir::AccessPath,
    ) -> SummaryFact<crate::hir_facts::Incidence> {
        self.summaries.template_internal_signal_incidence(self.facts, self.evidence, path)
    }

    /// Validate this fact snapshot once for a batch of generated equation queries.
    #[must_use]
    pub fn template_generated_equations(&self) -> GeneratedEquationQueries<'a, 'facts> {
        self.summaries.template_generated_equations(self.facts, self.evidence)
    }

    /// Request two complete satisfying bit models in a validated leaf root scope.
    #[must_use]
    pub fn template_bit_ambiguity(
        &self,
        input: &AccessPath,
        bits: &[AccessPath],
    ) -> SummaryFact<BitAmbiguityOutcome> {
        self.summaries.template_bit_ambiguity(self.facts, self.evidence, input, bits)
    }

    /// Prove two complete bit models for checked ports in this root template.
    #[must_use]
    pub fn template_bit_ambiguity_handles(
        &self,
        input: &AccessHandle,
        bits: &[AccessHandle],
    ) -> SummaryFact<BitAmbiguityOutcome> {
        self.summaries.template_bit_ambiguity_handles(self.facts, self.evidence, input, bits)
    }

    /// Prove complete caller/child models for the sole component under this main scope.
    #[must_use]
    pub fn component_bit_ambiguity_handles(
        &self,
        applied: &AppliedComponentPort,
        input: &AccessHandle,
        bits: &[AccessHandle],
    ) -> SummaryFact<ComponentBitAmbiguityOutcome> {
        self.summaries.component_bit_ambiguity_handles(self.facts, applied, input, bits)
    }

    /// Prove complete caller and child models for checked child port schemas.
    #[must_use]
    pub fn component_bit_ambiguity_ports(
        &self,
        applied: &AppliedComponentPort,
        input: PortId,
        bits: PortId,
    ) -> SummaryFact<ComponentBitAmbiguityOutcome> {
        self.summaries.component_bit_ambiguity_ports(self.facts, applied, input, bits)
    }

    /// Prove a comparator range violation through the complete three-scope closure.
    #[must_use]
    pub fn component_comparator_range(
        &self,
        applied: &AppliedComponentPort,
    ) -> SummaryFact<Vec<crate::interprocedural::ComparatorRangeViolation>> {
        self.summaries.component_comparator_range(self.facts, applied)
    }

    /// Request a source-valid bit relation in this validated root template scope.
    #[must_use]
    pub fn template_bit_decomposition(
        &self,
        input: &AccessPath,
        bits: &[AccessPath],
    ) -> SummaryFact<Option<BitDecomposition>> {
        self.summaries.template_bit_decomposition(self.facts, self.evidence, input, bits)
    }

    /// Request a validated bit relation for exact ports in this root template.
    #[must_use]
    pub fn template_bit_decomposition_handles(
        &self,
        input: &AccessHandle,
        bits: &[AccessHandle],
    ) -> SummaryFact<Option<BitDecomposition>> {
        self.summaries.template_bit_decomposition_handles(self.facts, self.evidence, input, bits)
    }

    /// Enumerate every checked direct-child output in this exact source scope.
    ///
    /// Missing shapes, calls, or the bounded handle budget make the result
    /// unavailable, so a rule cannot treat a partial list as complete.
    #[must_use]
    pub fn exact_component_outputs(&self) -> SummaryFact<Vec<EnumeratedComponentOutput>> {
        self.summaries.exact_component_outputs(self.facts, self.evidence)
    }

    /// Prove that an exact exported output of the active main is read by its environment.
    ///
    /// Inputs, foreign handles, and library roots produce unavailable evidence.
    #[must_use]
    pub fn exported_main_output_use(&self, handle: &AccessHandle) -> SummaryFact<ProjectOutputUse> {
        self.summaries.exported_main_output_use(self.facts, self.evidence, handle)
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
        let DefinitionRef::Template(_) = self.call_context().definition() else { return None };
        Some(self.summaries.template_port_for_evidence(self.facts, self.evidence, port, indices))
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

    /// Record an undecided predicate in this validated scope without changing its reason or span.
    pub(super) fn abstention(
        &self,
        kind: RuleKind,
        span: Span,
        reason: AbstentionReason,
    ) -> ScopedAbstention {
        ScopedAbstention { kind, context: self.call_context().clone(), span, reason }
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
