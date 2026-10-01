use std::collections::{BTreeMap, BTreeSet};

use parser::hir::{
    DefinitionRef, ExprId, ExprKind, HirProject, LoweredProject, ProjectIdentity, SymbolId,
};
use parser::new_frontend::Version;
use program_structure::utils::constants::Curve;

use crate::hir_cfg::DefinitionCfg;
use crate::hir_facts::{
    analyze_with_scalar_parameters, exact_compile_time, AnalysisFacts, FactBlocker, FieldContext,
    FieldValue, Range,
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
                ArgumentValue::Array(_) | ArgumentValue::Bus(_) => {
                    return Err(SummaryBlocker::UnsupportedContext);
                }
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
    ExternalSummary,
    MissingReturn,
    LocalAnalysis(String),
    RecursiveCycle,
    ContextBudget,
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

    /// Analyze one definition under a validated source scope and bind the result to it.
    pub fn analyze_for_evidence<'b>(
        &'b self,
        cfg: &'b DefinitionCfg,
        evidence: &ContextEvidence,
        budget: Option<usize>,
    ) -> Result<AnalysisFacts<'b>, SummaryBlocker> {
        self.check_evidence(evidence)?;
        if cfg.definition() != evidence.context.definition {
            return Err(SummaryBlocker::WrongContext);
        }
        let parameters =
            self.parameters(cfg.definition()).ok_or(SummaryBlocker::ForeignDefinition)?;
        let seeds = evidence.context.scalar_seeds(parameters)?;
        let mut facts = analyze_with_scalar_parameters(self.hir(), cfg, &self.field, seeds, budget)
            .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
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

    use parser::hir::{lower_project, DefinitionRef};
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
        let lowered = lower_project(&loaded);
        let provider = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
        let DefinitionRef::Template(template) = lowered.hir.definition("T").unwrap() else {
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
}
