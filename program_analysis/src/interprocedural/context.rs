use std::collections::{BTreeMap, BTreeSet};

use parser::hir::{DefinitionRef, ExprId, ExprKind, HirProject, LoweredProject, ProjectIdentity};
use parser::new_frontend::Version;
use program_structure::utils::constants::Curve;

use crate::hir_facts::{
    exact_compile_time, AnalysisFacts, FactBlocker, FieldContext, FieldValue, Range,
};

use super::{build_call_graph, CallGraph, CallGraphError, CallOwner, CallSiteId, ReachableCall};

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
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SummaryBlocker {
    ForeignDefinition,
    ForeignCall,
    WrongContext,
    WrongArity { expected: usize, actual: usize },
    UnprovenArgument(ExprId),
    UnsupportedCallForm,
    LocalFacts(BTreeSet<FactBlocker>),
}

/// Owns the validated field and graph used to construct summary contexts.
pub struct ProjectSummaries<'a> {
    lowered: &'a LoweredProject,
    field: FieldContext,
    graph: CallGraph,
}

impl<'a> ProjectSummaries<'a> {
    /// Build a provider for one selected compiler curve and the lowered language version.
    pub fn build(lowered: &'a LoweredProject, curve: Curve) -> Result<Self, CallGraphError> {
        let graph = build_call_graph(&lowered.hir)?;
        Ok(Self { lowered, field: FieldContext::for_curve(curve), graph })
    }

    #[must_use]
    pub fn hir(&self) -> &HirProject {
        &self.lowered.hir
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
            project: self.lowered.hir.identity(),
            definition,
            curve: self.field.curve().into(),
            version: self.lowered.version,
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
        if context.project != self.lowered.hir.identity()
            || context.curve != self.field.curve().into()
            || context.version != self.lowered.version
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
    ) -> Result<ContextEvidence, SummaryBlocker> {
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
        let context = self.context_for(call.callee(), arguments)?;
        Ok(ContextEvidence { context, origin: ContextOrigin::Call(site.id()) })
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

    fn exact_main_arguments(
        &self,
        arguments: &[ExprId],
    ) -> Result<Vec<ArgumentValue>, SummaryBlocker> {
        let mut values = Vec::with_capacity(arguments.len());
        for expression in arguments {
            let value = exact_compile_time(self.hir(), &self.field, *expression)
                .ok_or(SummaryBlocker::UnprovenArgument(*expression))?;
            values.push(ArgumentValue::Scalar(value));
        }
        Ok(values)
    }

    fn exact_call_arguments(
        &self,
        arguments: &[ExprId],
        facts: &AnalysisFacts<'_>,
    ) -> Result<Vec<ArgumentValue>, SummaryBlocker> {
        let mut values = Vec::with_capacity(arguments.len());
        for expression in arguments {
            let range = facts.range(*expression);
            let Some(range) = range.certified() else {
                return Err(SummaryBlocker::LocalFacts(
                    range.unavailable().cloned().unwrap_or_default(),
                ));
            };
            let Range::Exact(value) = range else {
                return Err(SummaryBlocker::UnprovenArgument(*expression));
            };
            values.push(ArgumentValue::Scalar(value.clone()));
        }
        Ok(values)
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
