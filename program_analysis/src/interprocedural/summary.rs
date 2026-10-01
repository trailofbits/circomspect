use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::lattice::Lattice;
use abstract_interpretation::graph::FlowGraph;
use parser::hir::{DefinitionRef, ExprId, ExprKind, Function, FunctionId, SymbolId};

use crate::hir_cfg::{build_cfg, CfgNodeKind, DefinitionCfg};
use crate::hir_facts::{analyze_with_scalar_parameters, AnalysisFacts, Fact, FieldContext, Range};

use super::{CallContext, CallOwner, CallReachability, ProjectSummaries, SummaryBlocker};

/// A summary certificate is created only after the relevant CFG and calls are complete.
///
/// ```compile_fail
/// use circomspect_program_analysis::interprocedural::SummaryFact;
/// let forged = SummaryFact::known(1);
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SummaryFact<T>(SummaryState<T>);

#[derive(Clone, Debug, Eq, PartialEq)]
enum SummaryState<T> {
    Certified(T),
    Unavailable(BTreeSet<SummaryBlocker>),
}

impl<T> SummaryFact<T> {
    fn known(value: T) -> Self {
        Self(SummaryState::Certified(value))
    }

    fn blocked(blocker: SummaryBlocker) -> Self {
        Self(SummaryState::Unavailable(BTreeSet::from([blocker])))
    }

    pub(super) fn from_result(result: Result<T, SummaryBlocker>) -> Self {
        match result {
            Ok(value) => Self::known(value),
            Err(blocker) => Self::blocked(blocker),
        }
    }

    #[must_use]
    pub fn certified(&self) -> Option<&T> {
        match &self.0 {
            SummaryState::Certified(value) => Some(value),
            SummaryState::Unavailable(_) => None,
        }
    }

    #[must_use]
    pub fn unavailable(&self) -> Option<&BTreeSet<SummaryBlocker>> {
        match &self.0 {
            SummaryState::Certified(_) => None,
            SummaryState::Unavailable(blockers) => Some(blockers),
        }
    }
}

pub(super) fn certified<T>(fact: &Fact<T>) -> Result<&T, SummaryBlocker> {
    fact.certified()
        .ok_or_else(|| SummaryBlocker::LocalFacts(fact.unavailable().cloned().unwrap_or_default()))
}

/// Return evidence for one scalar function context.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionSummary {
    returns: Range,
    input_dependencies: BTreeSet<usize>,
}

impl FunctionSummary {
    #[must_use]
    pub fn returns(&self) -> &Range {
        &self.returns
    }

    #[must_use]
    pub fn input_dependencies(&self) -> &BTreeSet<usize> {
        &self.input_dependencies
    }
}

#[derive(Default)]
struct Evaluation {
    active: BTreeSet<CallContext>,
    memo: BTreeMap<CallContext, SummaryFact<FunctionSummary>>,
}

struct CalleeReturn {
    summary: FunctionSummary,
    arguments: Vec<ExprId>,
}

impl ProjectSummaries<'_> {
    /// Summarize a scalar function using checked CFG reachability and resolved call sites.
    pub fn function(&self, id: FunctionId, context: &CallContext) -> SummaryFact<FunctionSummary> {
        self.function_inner(id, context, &mut Evaluation::default())
    }

    fn function_inner(
        &self,
        id: FunctionId,
        context: &CallContext,
        evaluation: &mut Evaluation,
    ) -> SummaryFact<FunctionSummary> {
        const MAX_CONTEXTS: usize = 64;
        if let Some(cached) = evaluation.memo.get(context) {
            return cached.clone();
        }
        if evaluation.active.contains(context) {
            return SummaryFact::blocked(SummaryBlocker::RecursiveCycle);
        }
        if evaluation.active.len() + evaluation.memo.len() >= MAX_CONTEXTS {
            return SummaryFact::blocked(SummaryBlocker::ContextBudget);
        }
        evaluation.active.insert(context.clone());
        let result = SummaryFact::from_result(self.compute_function(id, context, evaluation));
        evaluation.active.remove(context);
        evaluation.memo.insert(context.clone(), result.clone());
        result
    }

    fn compute_function(
        &self,
        id: FunctionId,
        context: &CallContext,
        evaluation: &mut Evaluation,
    ) -> Result<FunctionSummary, SummaryBlocker> {
        self.with_local_function(id, context, |function, cfg, facts| {
            let calls = self.collect_calls(id, facts, evaluation)?;
            self.summarize_returns(function, cfg, facts, &calls)
        })
    }

    pub(super) fn with_local_function<T>(
        &self,
        id: FunctionId,
        context: &CallContext,
        work: impl FnOnce(&Function, &DefinitionCfg, &AnalysisFacts<'_>) -> Result<T, SummaryBlocker>,
    ) -> Result<T, SummaryBlocker> {
        let Some(function) = self.hir().function(id) else {
            return Err(SummaryBlocker::ForeignDefinition);
        };
        if context.definition() != DefinitionRef::Function(id) {
            return Err(SummaryBlocker::WrongContext);
        }
        self.check_context(context)?;
        let parameters = context.scalar_seeds(&function.parameters)?;
        let cfg = build_cfg(self.hir(), DefinitionRef::Function(id))
            .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
        let field = FieldContext::for_curve(self.curve().clone());
        let facts = analyze_with_scalar_parameters(self.hir(), &cfg, &field, parameters, None)
            .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
        if let Some(expression) =
            self.invalid_deferred_assignment(&cfg, &function.parameters, context, &facts)
        {
            return Err(SummaryBlocker::InvalidAssignment(expression));
        }
        work(function, &cfg, &facts)
    }

    fn collect_calls(
        &self,
        id: FunctionId,
        facts: &AnalysisFacts<'_>,
        evaluation: &mut Evaluation,
    ) -> Result<BTreeMap<ExprId, CalleeReturn>, SummaryBlocker> {
        let owner = CallOwner::Definition(DefinitionRef::Function(id));
        let mut calls = BTreeMap::new();
        for site in self.graph().calls_from(owner) {
            let call = match self.graph().reachable_call(site.id(), facts) {
                CallReachability::Unreachable => continue,
                CallReachability::Reachable(call) => call,
                CallReachability::Unavailable(_) => return Err(SummaryBlocker::ExternalSummary),
            };
            let DefinitionRef::Function(callee) = call.callee() else {
                return Err(SummaryBlocker::ExternalSummary);
            };
            let expression = site.expression.ok_or(SummaryBlocker::UnsupportedCallForm)?;
            let Some(ExprKind::Call { arguments, .. }) =
                self.hir().expression(expression).map(|expr| &expr.kind)
            else {
                return Err(SummaryBlocker::UnsupportedCallForm);
            };
            let context = self.call_context(&call, facts)?;
            let summary = self.function_inner(callee, &context, evaluation);
            let Some(summary) = summary.certified() else {
                let blocker = summary.unavailable().and_then(|items| items.iter().next()).cloned();
                return Err(blocker.unwrap_or(SummaryBlocker::ExternalSummary));
            };
            calls.insert(
                expression,
                CalleeReturn { summary: summary.clone(), arguments: arguments.clone() },
            );
        }
        Ok(calls)
    }

    fn summarize_returns(
        &self,
        function: &Function,
        cfg: &crate::hir_cfg::DefinitionCfg,
        facts: &AnalysisFacts<'_>,
        calls: &BTreeMap<ExprId, CalleeReturn>,
    ) -> Result<FunctionSummary, SummaryBlocker> {
        let mut returns = Range::Unreachable;
        let mut observed = false;
        let mut dependencies = BTreeSet::new();
        for node in cfg.nodes() {
            let Some(CfgNodeKind::Return(expression)) = cfg.node(*node).map(|item| &item.kind)
            else {
                continue;
            };
            if !*certified(&facts.reachable_expression(*expression))? {
                continue;
            }
            let (range, used) = self.return_fact(*expression, facts, calls)?;
            returns.join_assign(&range);
            observed = true;
            for symbol in used {
                let index = function
                    .parameters
                    .iter()
                    .position(|item| *item == symbol)
                    .ok_or(SummaryBlocker::ExternalSummary)?;
                dependencies.insert(index);
            }
        }
        if !observed {
            return Err(SummaryBlocker::MissingReturn);
        }
        Ok(FunctionSummary { returns, input_dependencies: dependencies })
    }

    fn return_fact(
        &self,
        expression: ExprId,
        facts: &AnalysisFacts<'_>,
        calls: &BTreeMap<ExprId, CalleeReturn>,
    ) -> Result<(Range, BTreeSet<SymbolId>), SummaryBlocker> {
        if let Some(call) = calls.get(&expression) {
            let mut used = BTreeSet::new();
            for index in call.summary.input_dependencies() {
                let argument = call.arguments.get(*index).ok_or(SummaryBlocker::WrongContext)?;
                let dependencies = facts.dependencies(*argument);
                used.extend(certified(&dependencies)?.iter().map(|key| key.root));
            }
            return Ok((call.summary.returns().clone(), used));
        }
        let range = facts.range(expression);
        let dependencies = facts.dependencies(expression);
        Ok((
            certified(&range)?.clone(),
            certified(&dependencies)?.iter().map(|key| key.root).collect(),
        ))
    }
}
