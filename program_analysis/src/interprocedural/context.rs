use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use parser::hir::{DefinitionRef, ExprId, ExprKind, ProjectIdentity, SemanticDiagnostic, SymbolId};
use parser::frontend::{Span, Version};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::DefinitionCfg;
use crate::hir_facts::{exact_compile_time, AnalysisFacts, FactBlocker, FieldValue, Range};

use crate::interprocedural::{CallOwner, CallSite, CallSiteId, ProjectAnalysis, ReachableCall};

const MAX_ARGUMENT_NODES: usize = 4096;
pub(super) const MAX_ARGUMENT_DEPTH: usize = 64;

/// Shape of a compile-time argument before a concrete value is known.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ArgumentShape {
    Scalar,
    Array,
    Bus,
    Unknown,
}

/// A typed compile-time argument. `Symbolic` retains library contexts without a main.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ArgumentValue {
    Scalar(FieldValue),
    Array(Vec<Self>),
    Bus(BTreeMap<String, Self>),
    Symbolic(ArgumentShape),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum CurveKey {
    Bn254,
    Bls12_381,
    Goldilocks,
}

impl From<&Curve> for CurveKey {
    fn from(curve: &Curve) -> Self {
        match curve {
            Curve::Bn254 => Self::Bn254,
            Curve::Bls12_381 => Self::Bls12_381,
            Curve::Goldilocks => Self::Goldilocks,
        }
    }
}

/// A validated specialization key, bound to one HIR, field, version, and definition.
///
/// The context issuer validates project identity, language version, curve, definition, arity,
/// and canonical argument values/shapes. This owned key can describe a hypothetical call;
/// only separate context evidence authorizes analysis of a root or reachable call.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CallContext {
    project: ProjectIdentity,
    definition: DefinitionRef,
    curve: CurveKey,
    version: Version,
    arguments: Vec<ArgumentValue>,
}

impl CallContext {
    #[must_use]
    pub fn definition(&self) -> DefinitionRef {
        self.definition
    }

    #[must_use]
    pub fn version(&self) -> Version {
        self.version
    }

    #[must_use]
    pub fn arguments(&self) -> &[ArgumentValue] {
        &self.arguments
    }

    pub(crate) fn scalar_seeds(&self, parameters: &[SymbolId]) -> BTreeMap<SymbolId, FieldValue> {
        let mut values = BTreeMap::new();
        for (symbol, argument) in parameters.iter().zip(&self.arguments) {
            match argument {
                ArgumentValue::Scalar(value) => {
                    values.insert(*symbol, value.clone());
                }
                ArgumentValue::Symbolic(_) | ArgumentValue::Array(_) | ArgumentValue::Bus(_) => {}
            }
        }
        values
    }
}

/// Origin of a summary scope. Symbolic roots require universal proof before reporting.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ContextOrigin {
    SymbolicRoot,
    Main(CallSiteId),
    Call(CallSiteId),
}

/// One provider-issued source call in the exact path to a rule scope.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CallPathSite {
    site: CallSiteId,
    owner: CallOwner,
    callee: DefinitionRef,
    span: Span,
}

impl CallPathSite {
    fn from_site(site: &CallSite) -> Result<Self, SummaryBlocker> {
        let callee = site.resolved().ok_or(SummaryBlocker::ForeignCall)?;
        Ok(Self { site: site.id(), owner: site.owner, callee, span: site.span })
    }

    #[must_use]
    pub const fn span(self) -> Span {
        self.span
    }

    #[must_use]
    pub const fn owner(self) -> CallOwner {
        self.owner
    }

    #[must_use]
    pub const fn callee(self) -> DefinitionRef {
        self.callee
    }
}

impl Ord for CallPathSite {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.site, self.owner, self.callee, self.span.source(), self.span.start(), self.span.end())
            .cmp(&(
                other.site,
                other.owner,
                other.callee,
                other.span.source(),
                other.span.start(),
                other.span.end(),
            ))
    }
}

impl PartialOrd for CallPathSite {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// A nonforgeable scope linking a context to a library root or reachable call.
///
/// The context issuer binds a symbolic library root, main, or reachable call to its exact
/// project, field, root, and source call-site ancestry. Consumers must match this evidence to
/// local facts; equal argument values alone do not authorize evidence reuse.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ContextEvidence {
    context: CallContext,
    origin: ContextOrigin,
    call_path: Vec<CallPathSite>,
}

impl ContextEvidence {
    #[must_use]
    pub fn context(&self) -> &CallContext {
        &self.context
    }

    #[must_use]
    pub fn origin(&self) -> ContextOrigin {
        self.origin
    }

    pub(crate) fn call_path(&self) -> &[CallPathSite] {
        &self.call_path
    }
}

/// Why a context cannot be used as certified summary evidence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SummaryBlocker {
    ForeignDefinition,
    IncompleteDefinition,
    ForeignCall,
    WrongContext,
    WrongArity { expected: usize, actual: usize },
    UnprovenArgument(ExprId),
    UnsupportedCallForm,
    LocalFacts(BTreeSet<FactBlocker>),
    UnsupportedContext,
    InvalidAssignment(ExprId),
    InvalidValueUse(SymbolId),
    WrongInstance,
    DuplicateInstance,
    SymbolicInstance,
    MissingInputBinding,
    DuplicateInputBinding,
    WitnessOnlyInput,
    ExternalSummary,
    MissingReturn,
    LocalAnalysis(String),
    RecursiveCycle,
    ContextBudget,
}

/// A failed context analysis, retaining a located semantic error when specialization proves one.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AnalyzeEvidenceError {
    Blocked(SummaryBlocker),
    InvalidAssignment { context: Box<CallContext>, diagnostic: Box<SemanticDiagnostic> },
    InvalidValueUse { context: Box<CallContext>, diagnostic: Box<SemanticDiagnostic> },
}

impl AnalyzeEvidenceError {
    #[must_use]
    pub fn diagnostic(&self) -> Option<&SemanticDiagnostic> {
        match self {
            Self::InvalidAssignment { diagnostic, .. }
            | Self::InvalidValueUse { diagnostic, .. } => Some(diagnostic),
            Self::Blocked(_) => None,
        }
    }
}

impl ProjectAnalysis<'_> {
    /// Construct a key only when the definition and parameter count belong to this HIR.
    ///
    /// # Errors
    /// Returns a blocker for a foreign definition or a mismatched argument count.
    pub fn context_for(
        &self,
        definition: DefinitionRef,
        arguments: Vec<ArgumentValue>,
    ) -> Result<CallContext, SummaryBlocker> {
        let expected = self.parameter_count(definition).ok_or(SummaryBlocker::ForeignDefinition)?;
        if arguments.len() != expected {
            return Err(SummaryBlocker::WrongArity { expected, actual: arguments.len() });
        }
        let arguments = arguments.into_iter().map(|value| self.canonicalize(value)).collect();
        Ok(CallContext {
            project: self.hir().identity(),
            definition,
            curve: self.curve().into(),
            version: self.lifted_project().version,
            arguments,
        })
    }

    /// Create the universal library-root context without requiring a `main` instance.
    ///
    /// # Errors
    /// Returns a blocker when the definition does not belong to this project.
    pub fn symbolic_context_for(
        &self,
        definition: DefinitionRef,
    ) -> Result<CallContext, SummaryBlocker> {
        let count = self.parameter_count(definition).ok_or(SummaryBlocker::ForeignDefinition)?;
        self.context_for(definition, vec![ArgumentValue::Symbolic(ArgumentShape::Unknown); count])
    }

    /// Validate that a specialization key belongs to this provider.
    ///
    /// # Errors
    /// Returns a blocker for a different project, curve, version, definition, or arity.
    pub fn check_context(&self, context: &CallContext) -> Result<(), SummaryBlocker> {
        if context.project != self.hir().identity()
            || context.curve != self.curve().into()
            || context.version != self.lifted_project().version
        {
            return Err(SummaryBlocker::WrongContext);
        }
        let expected =
            self.parameter_count(context.definition).ok_or(SummaryBlocker::ForeignDefinition)?;
        if context.arguments.len() != expected {
            return Err(SummaryBlocker::WrongArity { expected, actual: context.arguments.len() });
        }
        Ok(())
    }

    /// A library definition is a scope even without a `main` instantiation.
    /// A finding still needs a predicate proved for all symbolic values.
    ///
    /// # Errors
    /// Returns a blocker when the definition does not belong to this project.
    pub fn symbolic_root(
        &self,
        definition: DefinitionRef,
    ) -> Result<ContextEvidence, SummaryBlocker> {
        Ok(ContextEvidence {
            context: self.symbolic_context_for(definition)?,
            origin: ContextOrigin::SymbolicRoot,
            call_path: Vec::new(),
        })
    }

    /// Bind a checked `main` call to independently proved compile-time arguments.
    ///
    /// # Errors
    /// Returns a blocker for a foreign main call or arguments that cannot be proved exact.
    pub fn main_evidence(
        &self,
        call: &ReachableCall<'_>,
    ) -> Result<ContextEvidence, SummaryBlocker> {
        let site = call.site();
        let CallOwner::Main(index) = site.owner else { return Err(SummaryBlocker::ForeignCall) };
        if self.graph().site(site.id()) != Some(site) {
            return Err(SummaryBlocker::ForeignCall);
        }
        let main = self.hir().mains().get(index).ok_or(SummaryBlocker::ForeignCall)?;
        if site.target != main.target || site.span != main.span {
            return Err(SummaryBlocker::ForeignCall);
        }
        let arguments = self.exact_main_arguments(&main.arguments)?;
        let context = self.context_for(call.callee(), arguments)?;
        Ok(ContextEvidence {
            context,
            origin: ContextOrigin::Main(site.id()),
            call_path: vec![CallPathSite::from_site(site)?],
        })
    }

    /// Bind a checked reachable definition call to certified exact argument values.
    ///
    /// # Errors
    /// Returns a blocker for mismatched facts, an invalid call scope, or unproved arguments.
    pub fn call_evidence(
        &self,
        call: &ReachableCall<'_>,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
    ) -> Result<ContextEvidence, SummaryBlocker> {
        if self.hir().identity() != facts.hir().identity() || self.curve() != facts.curve() {
            return Err(SummaryBlocker::ForeignCall);
        }
        self.check_facts_for_evidence(facts, caller)?;
        let context = self.call_context(call, facts)?;
        self.check_call_execution_scope(facts, caller)?;
        self.extend_call_evidence(call.site(), context, caller)
    }

    /// Bind a source-matched provisional function call after exact return refinement.
    ///
    /// The raw graph remains provisional. This certificate additionally requires a
    /// provider-owned exact call result, certified reachability, exact arguments,
    /// and local facts bound to the supplied caller ancestry.
    ///
    /// # Errors
    /// Returns a typed blocker when any required scope, call, or value proof is absent.
    pub fn refined_function_call_evidence(
        &self,
        site: CallSiteId,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
    ) -> Result<ContextEvidence, SummaryBlocker> {
        self.check_facts_for_evidence(facts, caller)?;
        let site = self.graph().site(site).ok_or(SummaryBlocker::ForeignCall)?;
        let context = self.exact_site_context(site, facts)?;
        self.check_call_execution_scope(facts, caller)?;
        self.extend_call_evidence(site, context, caller)
    }

    fn extend_call_evidence(
        &self,
        site: &CallSite,
        context: CallContext,
        caller: &ContextEvidence,
    ) -> Result<ContextEvidence, SummaryBlocker> {
        let mut call_path = caller.call_path.clone();
        call_path.push(CallPathSite::from_site(site)?);
        let evidence =
            ContextEvidence { context, origin: ContextOrigin::Call(site.id()), call_path };
        self.check_evidence(&evidence)?;
        Ok(evidence)
    }

    pub(super) fn call_context(
        &self,
        call: &ReachableCall<'_>,
        facts: &AnalysisFacts<'_>,
    ) -> Result<CallContext, SummaryBlocker> {
        let site = call.site();
        if self.hir().identity() != facts.hir().identity()
            || self.curve() != facts.curve()
            || self.graph().site(site.id()) != Some(site)
        {
            return Err(SummaryBlocker::ForeignCall);
        }
        let CallOwner::Definition(owner) = site.owner else {
            return Err(SummaryBlocker::ForeignCall);
        };
        if owner != facts.definition() {
            return Err(SummaryBlocker::ForeignCall);
        }
        let expression = site.expression.ok_or(SummaryBlocker::UnsupportedCallForm)?;
        let reachable = facts.reachable_expression(expression);
        match reachable.into_result() {
            Ok(true) => {}
            Ok(false) => return Err(SummaryBlocker::ForeignCall),
            Err(blockers) => return Err(SummaryBlocker::LocalFacts(blockers)),
        }
        let Some(expr) = self.hir().expression(expression) else {
            return Err(SummaryBlocker::ForeignCall);
        };
        let (ExprKind::Call { arguments, .. } | ExprKind::AnonymousComponent { arguments, .. }) =
            &expr.kind
        else {
            return Err(SummaryBlocker::UnsupportedCallForm);
        };
        let arguments = self.exact_call_arguments(arguments, facts)?;
        self.context_for(call.callee(), arguments)
    }

    /// Revalidate a scope before a rule combines it with local facts.
    ///
    /// # Errors
    /// Returns a blocker for an invalid context, root origin, or source call path.
    pub fn check_evidence(&self, evidence: &ContextEvidence) -> Result<(), SummaryBlocker> {
        self.check_context(&evidence.context)?;
        match evidence.origin {
            ContextOrigin::SymbolicRoot => {
                if !evidence
                    .context
                    .arguments
                    .iter()
                    .all(|value| matches!(value, ArgumentValue::Symbolic(ArgumentShape::Unknown)))
                {
                    return Err(SummaryBlocker::WrongContext);
                }
            }
            ContextOrigin::Main(_) | ContextOrigin::Call(_) => {}
        }
        self.check_call_path(evidence)
    }

    fn check_call_path(&self, evidence: &ContextEvidence) -> Result<(), SummaryBlocker> {
        Self::check_path_origin(evidence)?;
        if evidence.call_path.is_empty() {
            return Ok(());
        }
        let mut previous = None;
        for step in &evidence.call_path {
            previous = Some(self.check_path_site(*step, previous)?);
        }
        if previous != Some(evidence.context.definition) {
            return Err(SummaryBlocker::ForeignCall);
        }
        Ok(())
    }

    fn check_path_origin(evidence: &ContextEvidence) -> Result<(), SummaryBlocker> {
        match evidence.origin {
            ContextOrigin::SymbolicRoot => {
                if evidence.call_path.is_empty() {
                    Ok(())
                } else {
                    Err(SummaryBlocker::WrongContext)
                }
            }
            ContextOrigin::Main(id) => Self::check_main_path(id, &evidence.call_path),
            ContextOrigin::Call(id) => {
                if evidence.call_path.last().is_some_and(|site| site.site == id) {
                    Ok(())
                } else {
                    Err(SummaryBlocker::ForeignCall)
                }
            }
        }
    }

    fn check_main_path(id: CallSiteId, path: &[CallPathSite]) -> Result<(), SummaryBlocker> {
        let [site] = path else { return Err(SummaryBlocker::ForeignCall) };
        if site.site != id {
            return Err(SummaryBlocker::ForeignCall);
        }
        let CallOwner::Main(_) = site.owner else { return Err(SummaryBlocker::ForeignCall) };
        Ok(())
    }

    fn check_path_site(
        &self,
        step: CallPathSite,
        previous: Option<DefinitionRef>,
    ) -> Result<DefinitionRef, SummaryBlocker> {
        let site = self.graph().site(step.site).ok_or(SummaryBlocker::ForeignCall)?;
        if CallPathSite::from_site(site)? != step {
            return Err(SummaryBlocker::ForeignCall);
        }
        if let Some(previous) = previous {
            if step.owner != CallOwner::Definition(previous) {
                return Err(SummaryBlocker::ForeignCall);
            }
        }
        Ok(step.callee)
    }

    /// Analyze one definition under a validated source scope and bind the result to it.
    ///
    /// # Errors
    /// Returns a blocker for invalid scope or unavailable facts, or a located shape error.
    pub fn analyze_for_evidence<'b>(
        &'b self,
        cfg: &'b DefinitionCfg,
        evidence: &ContextEvidence,
        budget: Option<usize>,
    ) -> Result<AnalysisFacts<'b>, AnalyzeEvidenceError> {
        self.check_evidence(evidence).map_err(AnalyzeEvidenceError::Blocked)?;
        if cfg.definition() != evidence.context.definition {
            return Err(AnalyzeEvidenceError::Blocked(SummaryBlocker::WrongContext));
        }
        let parameters = self
            .parameters(cfg.definition())
            .ok_or(AnalyzeEvidenceError::Blocked(SummaryBlocker::ForeignDefinition))?;
        let seeds = evidence.context.scalar_seeds(parameters);
        let mut facts = self
            .refined_facts(evidence.context(), &seeds, budget)
            .map_err(AnalyzeEvidenceError::Blocked)?;
        if let Some(failure) = self.invalid_value_use(parameters, evidence.context(), &facts) {
            return Err(failure.into_analysis_error(evidence.context()));
        }
        facts.bind_evidence(evidence.clone());
        Ok(facts)
    }

    /// Check that local facts were computed under this exact certified source scope.
    ///
    /// # Errors
    /// Returns a blocker unless facts belong to this exact project, field, and scope.
    pub fn check_facts_for_evidence(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.check_evidence(evidence)?;
        if facts.hir().identity() != self.hir().identity()
            || facts.curve() != self.curve()
            || facts.definition() != evidence.context.definition
            || !facts.matches_evidence(evidence)
        {
            return Err(SummaryBlocker::WrongContext);
        }
        Ok(())
    }

    fn exact_main_arguments(
        &self,
        arguments: &[ExprId],
    ) -> Result<Vec<ArgumentValue>, SummaryBlocker> {
        let mut values = Vec::with_capacity(arguments.len());
        let mut remaining = MAX_ARGUMENT_NODES;
        for expression in arguments {
            values.push(self.exact_argument(*expression, None, 0, &mut remaining)?);
        }
        Ok(values)
    }

    pub(super) fn exact_call_arguments(
        &self,
        arguments: &[ExprId],
        facts: &AnalysisFacts<'_>,
    ) -> Result<Vec<ArgumentValue>, SummaryBlocker> {
        let mut values = Vec::with_capacity(arguments.len());
        let mut remaining = MAX_ARGUMENT_NODES;
        for expression in arguments {
            values.push(self.exact_argument(*expression, Some(facts), 0, &mut remaining)?);
        }
        Ok(values)
    }

    fn exact_argument(
        &self,
        expression: ExprId,
        facts: Option<&AnalysisFacts<'_>>,
        depth: usize,
        remaining: &mut usize,
    ) -> Result<ArgumentValue, SummaryBlocker> {
        if depth >= MAX_ARGUMENT_DEPTH || *remaining == 0 {
            return Err(SummaryBlocker::ContextBudget);
        }
        *remaining -= 1;
        let expression_node =
            self.hir().expression(expression).ok_or(SummaryBlocker::ForeignCall)?;
        if let ExprKind::Array(items) = &expression_node.kind {
            let mut values = Vec::with_capacity(items.len());
            for item in items {
                values.push(self.exact_argument(*item, facts, depth + 1, remaining)?);
            }
            return Ok(ArgumentValue::Array(values));
        }
        let Some(facts) = facts else {
            let value = exact_compile_time(self.hir(), self.field_context(), expression)
                .ok_or(SummaryBlocker::UnprovenArgument(expression))?;
            return Ok(ArgumentValue::Scalar(value));
        };
        let range = facts.range(expression);
        let range =
            range.as_result().map_err(|blockers| SummaryBlocker::LocalFacts(blockers.clone()))?;
        let Range::Exact(value) = range else {
            return Err(SummaryBlocker::UnprovenArgument(expression));
        };
        Ok(ArgumentValue::Scalar(value.clone()))
    }

    fn parameter_count(&self, definition: DefinitionRef) -> Option<usize> {
        self.parameters(definition).map(<[SymbolId]>::len)
    }

    fn parameters(&self, definition: DefinitionRef) -> Option<&[SymbolId]> {
        match definition {
            DefinitionRef::Function(id) => {
                self.hir().function(id).map(|item| item.parameters.as_slice())
            }
            DefinitionRef::Template(id) => {
                self.hir().template(id).map(|item| item.parameters.as_slice())
            }
            DefinitionRef::Bus(id) => self.hir().bus(id).map(|item| item.parameters.as_slice()),
        }
    }

    fn canonicalize(&self, value: ArgumentValue) -> ArgumentValue {
        match value {
            ArgumentValue::Scalar(value) => {
                ArgumentValue::Scalar(self.field_context().canonical(value.as_bigint().clone()))
            }
            ArgumentValue::Array(items) => ArgumentValue::Array(
                items.into_iter().map(|item| self.canonicalize(item)).collect(),
            ),
            ArgumentValue::Bus(fields) => ArgumentValue::Bus(
                fields.into_iter().map(|(name, item)| (name, self.canonicalize(item))).collect(),
            ),
            ArgumentValue::Symbolic(shape) => ArgumentValue::Symbolic(shape),
        }
    }
}

#[cfg(test)]
mod tests {
    use parser::hir::{lift_project, DefinitionRef, SemanticCode, Severity};
    use parser::frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::build_cfg;
    use crate::interprocedural::{
        ArgumentValue, CallOwner, CallReachability, ProjectAnalysis, SummaryBlocker,
    };

    #[test]
    fn parameter_lookup_keeps_definition_kind_and_project_identity() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-parameter-lookup-{}-{:?}",
            std::process::id(),
            std::thread::current().id(),
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let file = directory.join("case.circom");
        std::fs::write(
            &file,
            "function F(a,b){return a;} template T(a,b,c){} bus B(a){signal out;}",
        )
        .unwrap();
        let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let foreign = lift_project(&loaded);
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        for (name, count) in [("F", 2), ("T", 3), ("B", 1)] {
            let definition = lifted.hir.definition(name).unwrap();
            assert_eq!(provider.parameter_count(definition), Some(count));
            assert_eq!(provider.parameters(definition).unwrap().len(), count);
            assert_eq!(provider.parameter_count(foreign.hir.definition(name).unwrap()), None);
            assert_eq!(provider.parameters(foreign.hir.definition(name).unwrap()), None);
        }
    }

    #[test]
    fn a_symbolic_scope_cannot_borrow_a_reachable_origin() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-summary-binding-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        std::fs::write(&source, "template T(n){signal output y;y<==n;} component main=T(1);")
            .unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let DefinitionRef::Template(template) = lifted.hir.definition("T").unwrap() else {
            panic!("template T")
        };
        let site = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph().reachable_main_call(site.id(), provider.hir())
        else {
            panic!("main call")
        };
        let evidence = provider.main_evidence(&call).unwrap();
        let cfg = build_cfg(provider.hir(), DefinitionRef::Template(template)).unwrap();
        let symbolic = provider.symbolic_root(DefinitionRef::Template(template)).unwrap();
        let wrong = provider.analyze_for_evidence(&cfg, &symbolic, None).unwrap();
        assert_eq!(
            provider.check_facts_for_evidence(&wrong, &evidence),
            Err(SummaryBlocker::WrongContext)
        );
    }

    #[test]
    fn invalid_deferred_write_cannot_bind_complete_array_context_facts() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-array-binding-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        let source_text =
            "template T(n){var x=n;x=1;signal output y;y<==1;} component main=T([1,2]);";
        std::fs::write(&source, source_text).unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("T").unwrap();
        let main = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph().reachable_main_call(main.id(), provider.hir())
        else {
            panic!("main call")
        };
        let evidence = provider.main_evidence(&call).unwrap();
        assert_eq!(
            evidence.context().arguments(),
            [ArgumentValue::Array(vec![
                ArgumentValue::Scalar(provider.field_context().canonical(1.into())),
                ArgumentValue::Scalar(provider.field_context().canonical(2.into())),
            ])]
        );
        let cfg = build_cfg(provider.hir(), definition).unwrap();
        let error = provider.analyze_for_evidence(&cfg, &evidence, None).err().unwrap();
        let super::AnalyzeEvidenceError::InvalidAssignment { context, diagnostic } = error else {
            panic!("aggregate assignment must emit a located error")
        };
        assert_eq!(*context, *evidence.context());
        assert_eq!(diagnostic.code, SemanticCode::InvalidAssignment);
        assert_eq!(diagnostic.code.as_str(), "T2000");
        assert_eq!(diagnostic.severity, Severity::Error);
        assert_eq!(&source_text[diagnostic.span.start()..diagnostic.span.end()], "n");
    }

    #[test]
    fn aggregate_argument_depth_budget_abstains_without_a_context() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-array-depth-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        let nested = format!(
            "{}1{}",
            "[".repeat(super::MAX_ARGUMENT_DEPTH),
            "]".repeat(super::MAX_ARGUMENT_DEPTH)
        );
        std::fs::write(&source, format!("template T(n){{}} component main=T({nested});")).unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let site = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph().reachable_main_call(site.id(), provider.hir())
        else {
            panic!("main call must be reachable")
        };
        assert_eq!(provider.main_evidence(&call), Err(SummaryBlocker::ContextBudget));
    }
}
