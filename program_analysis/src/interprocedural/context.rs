use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::FlowGraph;
use parser::hir::{
    DefinitionRef, ExprId, ExprKind, HirProject, LiftedProject, ProjectIdentity, SemanticCode,
    SemanticDiagnostic, Severity, SymbolId,
};
use parser::new_frontend::Version;
use program_structure::utils::constants::Curve;

use crate::hir_cfg::{CfgNodeKind, DefinitionCfg};
use crate::hir_facts::{
    analyze_with_scalar_parameters, exact_compile_time, AnalysisFacts, FactBlocker, FieldContext,
    FieldValue, Range,
};

use super::{build_call_graph, CallGraph, CallGraphError, CallOwner, CallSiteId, ReachableCall};

const MAX_ARGUMENT_NODES: usize = 4096;
const MAX_ARGUMENT_DEPTH: usize = 64;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ProvedValueShape {
    Scalar,
    Aggregate,
    Unknown,
}

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

    pub(crate) fn scalar_seeds(
        &self,
        parameters: &[SymbolId],
    ) -> Result<BTreeMap<SymbolId, FieldValue>, SummaryBlocker> {
        let mut values = BTreeMap::new();
        for (symbol, argument) in parameters.iter().zip(&self.arguments) {
            match argument {
                ArgumentValue::Scalar(value) => {
                    values.insert(*symbol, value.clone());
                }
                ArgumentValue::Symbolic(_) => {}
                ArgumentValue::Array(_) | ArgumentValue::Bus(_) => {}
            }
        }
        Ok(values)
    }
}

/// Origin of a summary scope. Symbolic roots require universal proof before reporting.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ContextOrigin {
    SymbolicRoot,
    Main(CallSiteId),
    Call(CallSiteId),
}

/// A nonforgeable scope linking a context to a library root or reachable call.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ContextEvidence {
    context: CallContext,
    origin: ContextOrigin,
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
}

/// Why a context cannot be used as certified summary evidence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SummaryBlocker {
    ForeignDefinition,
    ForeignCall,
    WrongContext,
    WrongArity { expected: usize, actual: usize },
    UnprovenArgument(ExprId),
    UnsupportedCallForm,
    LocalFacts(BTreeSet<FactBlocker>),
    UnsupportedContext,
    InvalidAssignment(ExprId),
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
}

impl AnalyzeEvidenceError {
    #[must_use]
    pub fn diagnostic(&self) -> Option<&SemanticDiagnostic> {
        match self {
            Self::InvalidAssignment { diagnostic, .. } => Some(diagnostic),
            Self::Blocked(_) => None,
        }
    }
}

/// Owns the validated field and graph used to construct summary contexts.
pub struct ProjectSummaries<'a> {
    lifted: &'a LiftedProject,
    field: FieldContext,
    graph: CallGraph,
}

impl<'a> ProjectSummaries<'a> {
    /// Build a provider for one selected compiler curve and the lifted language version.
    pub fn build(lifted: &'a LiftedProject, curve: Curve) -> Result<Self, CallGraphError> {
        let graph = build_call_graph(&lifted.hir)?;
        Ok(Self { lifted, field: FieldContext::for_curve(curve), graph })
    }

    #[must_use]
    pub fn hir(&self) -> &HirProject {
        &self.lifted.hir
    }

    #[must_use]
    pub fn graph(&self) -> &CallGraph {
        &self.graph
    }

    #[must_use]
    pub fn curve(&self) -> &Curve {
        self.field.curve()
    }

    /// Construct a key only when the definition and parameter count belong to this HIR.
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
            project: self.lifted.hir.identity(),
            definition,
            curve: self.field.curve().into(),
            version: self.lifted.version,
            arguments,
        })
    }

    /// Create the universal library-root context without requiring a `main` instance.
    pub fn symbolic_context_for(
        &self,
        definition: DefinitionRef,
    ) -> Result<CallContext, SummaryBlocker> {
        let count = self.parameter_count(definition).ok_or(SummaryBlocker::ForeignDefinition)?;
        self.context_for(definition, vec![ArgumentValue::Symbolic(ArgumentShape::Unknown); count])
    }

    pub fn check_context(&self, context: &CallContext) -> Result<(), SummaryBlocker> {
        if context.project != self.lifted.hir.identity()
            || context.curve != self.field.curve().into()
            || context.version != self.lifted.version
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
    pub fn symbolic_root(
        &self,
        definition: DefinitionRef,
    ) -> Result<ContextEvidence, SummaryBlocker> {
        Ok(ContextEvidence {
            context: self.symbolic_context_for(definition)?,
            origin: ContextOrigin::SymbolicRoot,
        })
    }

    /// Bind a checked `main` call to independently proved compile-time arguments.
    pub fn main_evidence(
        &self,
        call: &ReachableCall<'_>,
    ) -> Result<ContextEvidence, SummaryBlocker> {
        let site = call.site();
        let CallOwner::Main(index) = site.owner else { return Err(SummaryBlocker::ForeignCall) };
        if self.graph.site(site.id()) != Some(site) {
            return Err(SummaryBlocker::ForeignCall);
        }
        let main = self.hir().mains().get(index).ok_or(SummaryBlocker::ForeignCall)?;
        if site.target != main.target || site.span != main.span {
            return Err(SummaryBlocker::ForeignCall);
        }
        let arguments = self.exact_main_arguments(&main.arguments)?;
        let context = self.context_for(call.callee(), arguments)?;
        Ok(ContextEvidence { context, origin: ContextOrigin::Main(site.id()) })
    }

    /// Bind a checked reachable definition call to certified exact argument values.
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
        Ok(ContextEvidence { context, origin: ContextOrigin::Call(call.site().id()) })
    }

    pub(super) fn call_context(
        &self,
        call: &ReachableCall<'_>,
        facts: &AnalysisFacts<'_>,
    ) -> Result<CallContext, SummaryBlocker> {
        let site = call.site();
        if self.hir().identity() != facts.hir().identity()
            || self.curve() != facts.curve()
            || self.graph.site(site.id()) != Some(site)
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
        match reachable.certified() {
            Some(true) => {}
            Some(false) => return Err(SummaryBlocker::ForeignCall),
            None => {
                return Err(SummaryBlocker::LocalFacts(
                    reachable.unavailable().cloned().unwrap_or_default(),
                ));
            }
        }
        let Some(expr) = self.hir().expression(expression) else {
            return Err(SummaryBlocker::ForeignCall);
        };
        let arguments = match &expr.kind {
            ExprKind::Call { arguments, .. } | ExprKind::AnonymousComponent { arguments, .. } => {
                arguments
            }
            _ => return Err(SummaryBlocker::UnsupportedCallForm),
        };
        let arguments = self.exact_call_arguments(arguments, facts)?;
        self.context_for(call.callee(), arguments)
    }

    /// Revalidate a scope before a rule combines it with local facts.
    pub fn check_evidence(&self, evidence: &ContextEvidence) -> Result<(), SummaryBlocker> {
        self.check_context(&evidence.context)?;
        match evidence.origin {
            ContextOrigin::SymbolicRoot => {
                if evidence
                    .context
                    .arguments
                    .iter()
                    .all(|value| matches!(value, ArgumentValue::Symbolic(ArgumentShape::Unknown)))
                {
                    Ok(())
                } else {
                    Err(SummaryBlocker::WrongContext)
                }
            }
            ContextOrigin::Main(id) | ContextOrigin::Call(id) => {
                let site = self.graph.site(id).ok_or(SummaryBlocker::ForeignCall)?;
                if site.resolved() == Some(evidence.context.definition) {
                    Ok(())
                } else {
                    Err(SummaryBlocker::ForeignCall)
                }
            }
        }
    }

    /// Analyze one definition under a validated source scope and bind the result to it.
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
        let seeds =
            evidence.context.scalar_seeds(parameters).map_err(AnalyzeEvidenceError::Blocked)?;
        let mut facts = analyze_with_scalar_parameters(self.hir(), cfg, &self.field, seeds, budget)
            .map_err(|error| {
                AnalyzeEvidenceError::Blocked(SummaryBlocker::LocalAnalysis(format!("{error:?}")))
            })?;
        if let Some(expression) =
            self.invalid_deferred_assignment(cfg, parameters, evidence.context(), &facts)
        {
            let span = self
                .hir()
                .expression(expression)
                .ok_or(AnalyzeEvidenceError::Blocked(SummaryBlocker::ForeignDefinition))?
                .span;
            let diagnostic = SemanticDiagnostic {
                code: SemanticCode::InvalidAssignment,
                severity: Severity::Error,
                span,
                message: "a scalar variable assignment received an aggregate argument".into(),
                expected_kind: None,
                actual_kind: None,
            };
            return Err(AnalyzeEvidenceError::InvalidAssignment {
                context: Box::new(evidence.context.clone()),
                diagnostic: Box::new(diagnostic),
            });
        }
        facts.bind_context(evidence.context.clone());
        Ok(facts)
    }

    /// Check that local facts were computed under this exact certified source scope.
    pub fn check_facts_for_evidence(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.check_evidence(evidence)?;
        if facts.hir().identity() != self.hir().identity()
            || facts.curve() != self.curve()
            || facts.definition() != evidence.context.definition
            || !facts.matches_context(&evidence.context)
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

    fn exact_call_arguments(
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
            let value = exact_compile_time(self.hir(), &self.field, expression)
                .ok_or(SummaryBlocker::UnprovenArgument(expression))?;
            return Ok(ArgumentValue::Scalar(value));
        };
        let range = facts.range(expression);
        let Some(range) = range.certified() else {
            return Err(SummaryBlocker::LocalFacts(
                range.unavailable().cloned().unwrap_or_default(),
            ));
        };
        let Range::Exact(value) = range else {
            return Err(SummaryBlocker::UnprovenArgument(expression));
        };
        Ok(ArgumentValue::Scalar(value.clone()))
    }

    fn parameter_count(&self, definition: DefinitionRef) -> Option<usize> {
        match definition {
            DefinitionRef::Function(id) => {
                self.hir().function(id).map(|item| item.parameters.len())
            }
            DefinitionRef::Template(id) => {
                self.hir().template(id).map(|item| item.parameters.len())
            }
            DefinitionRef::Bus(id) => self.hir().bus(id).map(|item| item.parameters.len()),
        }
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

    pub(crate) fn invalid_deferred_assignment(
        &self,
        cfg: &DefinitionCfg,
        parameters: &[SymbolId],
        context: &CallContext,
        facts: &AnalysisFacts<'_>,
    ) -> Option<ExprId> {
        let aggregate: BTreeSet<_> = parameters
            .iter()
            .zip(context.arguments())
            .filter_map(|(symbol, argument)| match argument {
                ArgumentValue::Array(_) | ArgumentValue::Bus(_) => Some(*symbol),
                ArgumentValue::Scalar(_) | ArgumentValue::Symbolic(_) => None,
            })
            .collect();
        if aggregate.is_empty() {
            return None;
        }
        for id in cfg.nodes() {
            let Some(CfgNodeKind::DeferredAssignment { value, .. }) =
                cfg.node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            if self.proved_value_shape(*value, &aggregate, facts, 0) == ProvedValueShape::Aggregate
                && facts.reachable_node(*id).certified() == Some(&true)
                && facts.structurally_must_execute(*id)
            {
                return Some(*value);
            }
        }
        None
    }

    fn proved_value_shape(
        &self,
        expression: ExprId,
        aggregate: &BTreeSet<SymbolId>,
        facts: &AnalysisFacts<'_>,
        depth: usize,
    ) -> ProvedValueShape {
        if depth >= MAX_ARGUMENT_DEPTH {
            return ProvedValueShape::Unknown;
        }
        let Some(expression) = self.hir().expression(expression) else {
            return ProvedValueShape::Unknown;
        };
        match &expression.kind {
            ExprKind::Number(_) => ProvedValueShape::Scalar,
            ExprKind::Array(_) | ExprKind::Tuple(_) => ProvedValueShape::Aggregate,
            ExprKind::Access(path) if aggregate.contains(&path.root) && path.steps.is_empty() => {
                ProvedValueShape::Aggregate
            }
            ExprKind::Ternary { condition, yes, no } => {
                self.ternary_value_shape(*condition, *yes, *no, aggregate, facts, depth)
            }
            ExprKind::Parallel(inner) => {
                self.proved_value_shape(*inner, aggregate, facts, depth + 1)
            }
            ExprKind::Access(_)
            | ExprKind::Call { .. }
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Opaque(_) => ProvedValueShape::Unknown,
        }
    }

    fn ternary_value_shape(
        &self,
        condition: ExprId,
        yes: ExprId,
        no: ExprId,
        aggregate: &BTreeSet<SymbolId>,
        facts: &AnalysisFacts<'_>,
        depth: usize,
    ) -> ProvedValueShape {
        if let Some(Range::Exact(value)) = facts.range(condition).certified() {
            let selected = if self.field.is_zero(value) { no } else { yes };
            return self.proved_value_shape(selected, aggregate, facts, depth + 1);
        }
        let yes = self.proved_value_shape(yes, aggregate, facts, depth + 1);
        let no = self.proved_value_shape(no, aggregate, facts, depth + 1);
        if yes == no {
            yes
        } else {
            ProvedValueShape::Unknown
        }
    }

    fn canonicalize(&self, value: ArgumentValue) -> ArgumentValue {
        match value {
            ArgumentValue::Scalar(value) => {
                ArgumentValue::Scalar(self.field.canonical(value.as_bigint().clone()))
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
    use std::collections::BTreeMap;

    use parser::hir::{lift_project, DefinitionRef, SemanticCode, Severity};
    use parser::new_frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::build_cfg;
    use crate::hir_facts::analyze_with_scalar_parameters;
    use crate::interprocedural::{
        ArgumentValue, CallOwner, CallReachability, ProjectSummaries, SummaryBlocker,
    };

    #[test]
    fn a_different_concrete_seed_cannot_borrow_a_reachable_origin() {
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
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let DefinitionRef::Template(template) = lifted.hir.definition("T").unwrap() else {
            panic!("template T")
        };
        let site = provider.graph.calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph.reachable_main_call(site.id(), provider.hir())
        else {
            panic!("main call")
        };
        let evidence = provider.main_evidence(&call).unwrap();
        let two = provider
            .context_for(
                DefinitionRef::Template(template),
                vec![ArgumentValue::Scalar(provider.field.canonical(2.into()))],
            )
            .unwrap();
        let cfg = build_cfg(provider.hir(), DefinitionRef::Template(template)).unwrap();
        let parameter = provider.hir().template(template).unwrap().parameters[0];
        let mut wrong = analyze_with_scalar_parameters(
            provider.hir(),
            &cfg,
            &provider.field,
            BTreeMap::from([(parameter, provider.field.canonical(2.into()))]),
            None,
        )
        .unwrap();
        wrong.bind_context(two);
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
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("T").unwrap();
        let main = provider.graph.calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph.reachable_main_call(main.id(), provider.hir())
        else {
            panic!("main call")
        };
        let evidence = provider.main_evidence(&call).unwrap();
        assert_eq!(
            evidence.context().arguments(),
            [ArgumentValue::Array(vec![
                ArgumentValue::Scalar(provider.field.canonical(1.into())),
                ArgumentValue::Scalar(provider.field.canonical(2.into())),
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
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let site = provider.graph.calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph.reachable_main_call(site.id(), provider.hir())
        else {
            panic!("main call must be reachable")
        };
        assert_eq!(provider.main_evidence(&call), Err(SummaryBlocker::ContextBudget));
    }
}
