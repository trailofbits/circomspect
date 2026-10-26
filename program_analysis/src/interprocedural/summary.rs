use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{IndexedGraph, NodeId};
use abstract_interpretation::graph::FlowGraph;
use abstract_interpretation::lattice::Lattice;
use abstract_interpretation::solver::{
    solve, Blocker, DataflowAnalysis, Forward, SolveResult, Transfer, TransferOutcome,
};
use parser::hir::{DefinitionRef, ExprId, ExprKind, Function, FunctionId};

use crate::hir_cfg::{CfgNodeKind, DefinitionCfg};
use crate::hir_facts::{exact_compile_time, AnalysisFacts, Fact, FieldContext, Range};

use crate::interprocedural::{
    CallContext, CallOwner, CallReachability, ProjectAnalysis, SummaryBlocker,
};

/// Provider-owned evidence for a scoped summary; value-specific coverage remains explicit.
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
    pub(super) fn known(value: T) -> Self {
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
    fact.as_result().map_err(|blockers| SummaryBlocker::LocalFacts(blockers.clone()))
}

/// A return value's proof scope, which callers must inspect explicitly.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReturnEvidence<'a> {
    Complete(&'a Range),
    Conditional(&'a Range),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ReturnCoverage {
    Complete,
    Conditional,
}

/// Return evidence for one scalar function context.
///
/// A conditional value describes a return only if execution reaches it; it cannot establish
/// termination or complete return coverage. Repeated call contexts never produce a summary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionSummary {
    returns: Range,
    input_dependencies: BTreeSet<usize>,
    coverage: ReturnCoverage,
}

impl FunctionSummary {
    /// Return a value only when every reachable path completes a return.
    #[must_use]
    pub fn complete_return(&self) -> Option<&Range> {
        if self.coverage == ReturnCoverage::Complete {
            Some(&self.returns)
        } else {
            None
        }
    }

    /// Distinguish a complete return from a value conditional on reaching it.
    #[must_use]
    pub fn return_evidence(&self) -> ReturnEvidence<'_> {
        match self.coverage {
            ReturnCoverage::Complete => ReturnEvidence::Complete(&self.returns),
            ReturnCoverage::Conditional => ReturnEvidence::Conditional(&self.returns),
        }
    }

    #[must_use]
    pub fn input_dependencies(&self) -> &BTreeSet<usize> {
        &self.input_dependencies
    }
}

impl Lattice for FunctionSummary {
    fn bottom() -> Self {
        Self {
            returns: Range::Unreachable,
            input_dependencies: BTreeSet::new(),
            coverage: ReturnCoverage::Complete,
        }
    }

    fn leq(&self, other: &Self) -> bool {
        self.returns.leq(&other.returns)
            && self.input_dependencies.is_subset(&other.input_dependencies)
            && self.coverage <= other.coverage
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        let changed_range = self.returns.join_assign(&other.returns);
        let prior = self.input_dependencies.len();
        self.input_dependencies.extend(&other.input_dependencies);
        let prior_coverage = self.coverage;
        self.coverage = self.coverage.max(other.coverage);
        changed_range || self.input_dependencies.len() != prior || self.coverage != prior_coverage
    }
}

#[derive(Clone)]
struct ReturnCall {
    callee: CallContext,
    arguments: Vec<Result<BTreeSet<usize>, SummaryBlocker>>,
}

struct ReturnRecord {
    local: FunctionSummary,
    return_calls: Vec<ReturnCall>,
    control_callees: BTreeSet<CallContext>,
}

enum ReturnNode {
    Source,
    Context(FunctionSummary),
}

enum ReturnEdge {
    Source,
    Coverage,
    Call {
        arguments: Vec<Result<BTreeSet<usize>, SummaryBlocker>>,
        all_parameters: BTreeSet<usize>,
    },
}

struct ReturnAnalysis;

impl DataflowAnalysis<IndexedGraph<ReturnNode, ReturnEdge>> for ReturnAnalysis {
    type State = FunctionSummary;
    type Reason = SummaryBlocker;

    fn boundary(&self, _: NodeId) -> Self::State {
        FunctionSummary::bottom()
    }
}

impl Transfer<ReturnAnalysis, FunctionSummary, SummaryBlocker> for ReturnNode {
    fn apply(
        &self,
        _: &ReturnAnalysis,
        input: &FunctionSummary,
    ) -> TransferOutcome<FunctionSummary, SummaryBlocker> {
        let mut output = input.clone();
        if let Self::Context(local) = self {
            output.join_assign(local);
        }
        TransferOutcome::Known(output)
    }
}

impl Transfer<ReturnAnalysis, FunctionSummary, SummaryBlocker> for ReturnEdge {
    fn apply(
        &self,
        _: &ReturnAnalysis,
        input: &FunctionSummary,
    ) -> TransferOutcome<FunctionSummary, SummaryBlocker> {
        let (arguments, all_parameters) = match self {
            Self::Source => return TransferOutcome::Known(input.clone()),
            Self::Coverage => {
                let mut coverage = FunctionSummary::bottom();
                coverage.coverage = input.coverage;
                return TransferOutcome::Known(coverage);
            }
            Self::Call { arguments, all_parameters } => (arguments, all_parameters),
        };
        if input.returns == Range::Unreachable {
            return TransferOutcome::Known(FunctionSummary::bottom());
        }
        let mut dependencies = BTreeSet::new();
        for index in &input.input_dependencies {
            let Some(argument) = arguments.get(*index) else {
                return TransferOutcome::Opaque {
                    provisional: FunctionSummary {
                        returns: input.returns.clone(),
                        input_dependencies: all_parameters.clone(),
                        coverage: input.coverage,
                    },
                    reason: SummaryBlocker::WrongContext,
                };
            };
            match argument {
                Ok(used) => dependencies.extend(used),
                Err(blocker) => {
                    return TransferOutcome::Opaque {
                        provisional: FunctionSummary {
                            returns: input.returns.clone(),
                            input_dependencies: all_parameters.clone(),
                            coverage: input.coverage,
                        },
                        reason: blocker.clone(),
                    };
                }
            }
        }
        TransferOutcome::Known(FunctionSummary {
            returns: input.returns.clone(),
            input_dependencies: dependencies,
            coverage: input.coverage,
        })
    }
}

impl ProjectAnalysis<'_> {
    /// Summarize a scalar function using checked CFG reachability and resolved call sites.
    pub fn function(&self, id: FunctionId, context: &CallContext) -> SummaryFact<FunctionSummary> {
        if self.hir().function(id).is_none() {
            return SummaryFact::blocked(SummaryBlocker::ForeignDefinition);
        }
        if context.definition() != DefinitionRef::Function(id) {
            return SummaryFact::blocked(SummaryBlocker::WrongContext);
        }
        if let Err(blocker) = self.check_context(context) {
            return SummaryFact::blocked(blocker);
        }
        self.caches.returns.get_or_compute(context.clone(), || {
            SummaryFact::from_result(self.compute_function(context))
        })
    }

    fn compute_function(&self, context: &CallContext) -> Result<FunctionSummary, SummaryBlocker> {
        const MAX_CONTEXTS: usize = 64;
        let mut records = BTreeMap::new();
        let mut pending = vec![context.clone()];
        while let Some(next) = pending.pop() {
            if records.contains_key(&next) {
                continue;
            }
            if records.len() >= MAX_CONTEXTS {
                return Err(SummaryBlocker::ContextBudget);
            }
            let record = self.return_record(&next)?;
            pending.extend(record.control_callees.iter().cloned());
            records.insert(next, record);
        }
        // Immutable compile-time arguments make a repeated context the same invocation state.
        if has_reachable_cycle(&records, context) {
            return Err(SummaryBlocker::RecursiveCycle);
        }
        let solution = solve_returns(&records, context)?;
        if solution.returns == Range::Unreachable {
            return Err(SummaryBlocker::MissingReturn);
        }
        Ok(solution)
    }

    fn return_record(&self, context: &CallContext) -> Result<ReturnRecord, SummaryBlocker> {
        let DefinitionRef::Function(id) = context.definition() else {
            return Err(SummaryBlocker::WrongContext);
        };
        self.with_local_function(id, context, |function, cfg, facts| {
            let calls = self.reachable_function_calls(id, function, facts)?;
            let (mut local, return_calls) = self.local_returns(function, cfg, facts, &calls)?;
            if self.may_fail_before_return(id, cfg, facts) || has_unreturned_path(cfg, facts) {
                local.coverage = ReturnCoverage::Conditional;
            }
            let control_callees = calls.values().map(|call| call.callee.clone()).collect();
            Ok(ReturnRecord { local, return_calls, control_callees })
        })
    }

    fn closed_constant_return(&self, cfg: &DefinitionCfg) -> Option<FunctionSummary> {
        let field = FieldContext::for_curve(self.curve().clone());
        let mut value = None;
        let mut current = cfg.entry();
        let mut visited = BTreeSet::new();
        while current != cfg.exit() {
            if !visited.insert(current) {
                return None;
            }
            let node = cfg.node(current)?;
            if let CfgNodeKind::Opaque(_) | CfgNodeKind::LoopHeader = &node.kind {
                return None;
            }
            if let CfgNodeKind::Return(expression) = &node.kind {
                value = Some(exact_compile_time(self.hir(), &field, *expression)?);
            }
            let mut next = None;
            for id in cfg.edges() {
                let edge = cfg.edge(*id)?;
                if edge.source == current && next.replace(edge.target).is_some() {
                    return None;
                }
            }
            current = next?;
        }
        Some(FunctionSummary {
            returns: Range::Exact(value?),
            input_dependencies: BTreeSet::new(),
            coverage: ReturnCoverage::Complete,
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
        let parameters = context.scalar_seeds(&function.parameters);
        self.with_refined_facts(context, &parameters, |cfg, facts| {
            if let Some(failure) = self.invalid_value_use(&function.parameters, context, facts) {
                return Err(failure.summary_blocker());
            }

            work(function, cfg, facts)
        })
    }

    fn reachable_function_calls(
        &self,
        id: FunctionId,
        function: &Function,
        facts: &AnalysisFacts<'_>,
    ) -> Result<BTreeMap<ExprId, ReturnCall>, SummaryBlocker> {
        let owner = CallOwner::Definition(DefinitionRef::Function(id));
        let mut calls = BTreeMap::new();
        for site in self.graph().calls_from(owner) {
            let Some(DefinitionRef::Function(_)) = site.resolved() else { continue };
            if site.provenance == super::CallProvenance::Provisional
                && site.expression.is_some_and(|id| facts.exact_call_value(id).is_some())
            {
                continue;
            }
            let call = match self.graph().reachable_call(site.id(), facts) {
                CallReachability::Unreachable => continue,
                CallReachability::Reachable(call) => call,
                CallReachability::Unavailable(_) => return Err(SummaryBlocker::ExternalSummary),
            };
            let expression = site.expression.ok_or(SummaryBlocker::UnsupportedCallForm)?;
            let Some(ExprKind::Call { arguments, .. }) =
                self.hir().expression(expression).map(|expr| &expr.kind)
            else {
                return Err(SummaryBlocker::UnsupportedCallForm);
            };
            let callee = self.call_context(&call, facts)?;
            let arguments = Self::argument_dependencies(function, arguments, facts);
            calls.insert(expression, ReturnCall { callee, arguments });
        }
        Ok(calls)
    }

    fn argument_dependencies(
        function: &Function,
        arguments: &[ExprId],
        facts: &AnalysisFacts<'_>,
    ) -> Vec<Result<BTreeSet<usize>, SummaryBlocker>> {
        let mut result = Vec::with_capacity(arguments.len());
        for argument in arguments {
            let dependencies = facts.dependencies(*argument);
            let mapped = certified(&dependencies).and_then(|keys| {
                let mut indices = BTreeSet::new();
                for key in keys {
                    let index = function
                        .parameters
                        .iter()
                        .position(|item| *item == key.root)
                        .ok_or(SummaryBlocker::ExternalSummary)?;
                    indices.insert(index);
                }
                Ok(indices)
            });
            result.push(mapped);
        }
        result
    }

    fn local_returns(
        &self,
        function: &Function,
        cfg: &DefinitionCfg,
        facts: &AnalysisFacts<'_>,
        calls: &BTreeMap<ExprId, ReturnCall>,
    ) -> Result<(FunctionSummary, Vec<ReturnCall>), SummaryBlocker> {
        if let Some(summary) = self.closed_constant_return(cfg) {
            return Ok((summary, Vec::new()));
        }
        let mut local = FunctionSummary::bottom();
        let mut return_calls = Vec::new();
        let mut observed = false;
        for node in cfg.nodes() {
            let Some(CfgNodeKind::Return(expression)) = cfg.node(*node).map(|item| &item.kind)
            else {
                continue;
            };
            if !*certified(&facts.reachable_expression(*expression))? {
                continue;
            }
            observed = true;
            if let Some(call) = calls.get(expression) {
                return_calls.push(call.clone());
                continue;
            }
            if let Some(ExprKind::Call { .. }) =
                self.hir().expression(*expression).map(|expr| &expr.kind)
            {
                if facts.exact_call_value(*expression).is_none() {
                    return Err(SummaryBlocker::ExternalSummary);
                }
            }
            let range = certified(&facts.range(*expression))?.clone();
            let dependencies = facts.dependencies(*expression);
            let mut used = BTreeSet::new();
            for key in certified(&dependencies)? {
                let index = function
                    .parameters
                    .iter()
                    .position(|item| *item == key.root)
                    .ok_or(SummaryBlocker::ExternalSummary)?;
                used.insert(index);
            }
            local.join_assign(&FunctionSummary {
                returns: range,
                input_dependencies: used,
                coverage: ReturnCoverage::Complete,
            });
        }
        if !observed {
            return Err(SummaryBlocker::MissingReturn);
        }
        Ok((local, return_calls))
    }
}

enum ReturnPathStep {
    Continue,
    Returned,
    Unreturned,
}

enum ReturnTraversal {
    Enter(NodeId),
    Leave(NodeId),
}

fn return_path_step(
    cfg: &DefinitionCfg,
    facts: &AnalysisFacts<'_>,
    current: NodeId,
) -> ReturnPathStep {
    match facts.reachable_node(current).certified() {
        Some(false) => return ReturnPathStep::Returned,
        None => return ReturnPathStep::Unreturned,
        Some(true) => {}
    }
    if current == cfg.exit() {
        return ReturnPathStep::Unreturned;
    }
    let Some(node) = cfg.node(current) else { return ReturnPathStep::Unreturned };
    if let CfgNodeKind::Return(_) = node.kind {
        ReturnPathStep::Returned
    } else {
        ReturnPathStep::Continue
    }
}

fn has_unreturned_path(cfg: &DefinitionCfg, facts: &AnalysisFacts<'_>) -> bool {
    let mut successors: BTreeMap<NodeId, Vec<NodeId>> = BTreeMap::new();
    for id in cfg.edges() {
        let Some(edge) = cfg.edge(*id) else { return true };
        successors.entry(edge.source).or_default().push(edge.target);
    }
    unreturned_path_from(cfg.entry(), &successors, |node| return_path_step(cfg, facts, node))
}

fn unreturned_path_from(
    entry: NodeId,
    successors: &BTreeMap<NodeId, Vec<NodeId>>,
    step: impl Fn(NodeId) -> ReturnPathStep,
) -> bool {
    let mut stack = vec![ReturnTraversal::Enter(entry)];
    let mut active = BTreeSet::new();
    let mut complete = BTreeSet::new();
    while let Some(task) = stack.pop() {
        match task {
            ReturnTraversal::Leave(node) => {
                active.remove(&node);
                complete.insert(node);
            }
            ReturnTraversal::Enter(node) => {
                match step(node) {
                    ReturnPathStep::Returned => continue,
                    ReturnPathStep::Unreturned => return true,
                    ReturnPathStep::Continue => {}
                }
                if active.contains(&node) {
                    return true;
                }
                if complete.contains(&node) {
                    continue;
                }
                let Some(children) = successors.get(&node) else { return true };
                active.insert(node);
                stack.push(ReturnTraversal::Leave(node));
                for child in children {
                    stack.push(ReturnTraversal::Enter(*child));
                }
            }
        }
    }
    false
}

fn solve_returns(
    records: &BTreeMap<CallContext, ReturnRecord>,
    root: &CallContext,
) -> Result<FunctionSummary, SummaryBlocker> {
    let mut nodes = vec![ReturnNode::Source];
    let mut indices = BTreeMap::new();
    for (context, record) in records {
        let id = NodeId::new(nodes.len());
        indices.insert(context.clone(), id);
        nodes.push(ReturnNode::Context(record.local.clone()));
    }
    let mut edges = Vec::new();
    for (context, record) in records {
        let caller = *indices.get(context).ok_or(SummaryBlocker::WrongContext)?;
        edges.push((NodeId::new(0), caller, ReturnEdge::Source));
        for callee in &record.control_callees {
            let callee = *indices.get(callee).ok_or(SummaryBlocker::WrongContext)?;
            edges.push((callee, caller, ReturnEdge::Coverage));
        }
        let all_parameters: BTreeSet<usize> = (0..context.arguments().len()).collect();
        for call in &record.return_calls {
            let callee = *indices.get(&call.callee).ok_or(SummaryBlocker::WrongContext)?;
            edges.push((
                callee,
                caller,
                ReturnEdge::Call {
                    arguments: call.arguments.clone(),
                    all_parameters: all_parameters.clone(),
                },
            ));
        }
    }
    let root = *indices.get(root).ok_or(SummaryBlocker::WrongContext)?;
    let graph = IndexedGraph::new(nodes, edges, vec![NodeId::new(0)], vec![root])
        .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
    let result = solve::<_, _, Forward>(&graph, &ReturnAnalysis, Some(100_000))
        .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
    let facts = match result {
        SolveResult::Complete(facts) => facts,
        SolveResult::Incomplete { blockers, .. } => {
            for blocker in blockers {
                if let Blocker::OpaqueNode { reason, .. } | Blocker::OpaqueEdge { reason, .. } =
                    blocker
                {
                    return Err(reason);
                }
            }
            return Err(SummaryBlocker::ContextBudget);
        }
    };
    facts
        .get(&root)
        .and_then(|item| item.output.clone())
        .ok_or(SummaryBlocker::LocalAnalysis("missing root return state".into()))
}

fn has_reachable_cycle(records: &BTreeMap<CallContext, ReturnRecord>, root: &CallContext) -> bool {
    fn visit(
        records: &BTreeMap<CallContext, ReturnRecord>,
        context: &CallContext,
        active: &mut BTreeSet<CallContext>,
        complete: &mut BTreeSet<CallContext>,
    ) -> bool {
        if active.contains(context) {
            return true;
        }
        if complete.contains(context) {
            return false;
        }
        active.insert(context.clone());
        let Some(record) = records.get(context) else { return true };
        for callee in &record.control_callees {
            if visit(records, callee, active, complete) {
                return true;
            }
        }
        active.remove(context);
        complete.insert(context.clone());
        false
    }

    visit(records, root, &mut BTreeSet::new(), &mut BTreeSet::new())
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use abstract_interpretation::graph::NodeId;
    use abstract_interpretation::lattice::Lattice;
    use abstract_interpretation::solver::{Transfer, TransferOutcome};
    use program_structure::utils::constants::Curve;

    use crate::hir_facts::{FieldContext, Range};

    use super::{
        unreturned_path_from, FunctionSummary, ReturnAnalysis, ReturnCoverage, ReturnEdge,
        ReturnNode, ReturnPathStep, SummaryBlocker,
    };

    fn output(outcome: TransferOutcome<FunctionSummary, SummaryBlocker>) -> FunctionSummary {
        match outcome {
            TransferOutcome::Known(state) => state,
            TransferOutcome::Opaque { provisional, .. } => provisional,
        }
    }

    #[test]
    fn long_return_path_and_back_edge_preserve_coverage() {
        let length = 30_000;
        let terminal = NodeId::new(length);
        let mut successors = BTreeMap::new();
        for index in 0..length {
            successors.insert(NodeId::new(index), vec![NodeId::new(index + 1)]);
        }
        assert!(!unreturned_path_from(NodeId::new(0), &successors, |node| {
            if node == terminal {
                ReturnPathStep::Returned
            } else {
                ReturnPathStep::Continue
            }
        }));
        assert!(unreturned_path_from(NodeId::new(0), &successors, |node| {
            if node == terminal {
                ReturnPathStep::Unreturned
            } else {
                ReturnPathStep::Continue
            }
        }));
        successors.insert(terminal, vec![NodeId::new(length - 1)]);
        assert!(unreturned_path_from(NodeId::new(0), &successors, |_| {
            ReturnPathStep::Continue
        }));
    }

    #[test]
    fn production_return_join_and_transfers_are_monotone() {
        let field = FieldContext::for_curve(Curve::Bn254);
        let exact = Range::Exact(field.canonical(0.into()));
        let other = Range::Exact(field.canonical(1.into()));
        let states = [
            FunctionSummary::bottom(),
            FunctionSummary {
                returns: exact.clone(),
                input_dependencies: BTreeSet::new(),
                coverage: ReturnCoverage::Complete,
            },
            FunctionSummary {
                returns: exact,
                input_dependencies: BTreeSet::from([0]),
                coverage: ReturnCoverage::Complete,
            },
            FunctionSummary {
                returns: Range::Exact(field.canonical(0.into())),
                input_dependencies: BTreeSet::from([0]),
                coverage: ReturnCoverage::Conditional,
            },
            FunctionSummary {
                returns: other,
                input_dependencies: BTreeSet::new(),
                coverage: ReturnCoverage::Conditional,
            },
            FunctionSummary {
                returns: Range::Canonical,
                input_dependencies: BTreeSet::from([0]),
                coverage: ReturnCoverage::Complete,
            },
            FunctionSummary {
                returns: Range::Canonical,
                input_dependencies: BTreeSet::from([0, 1]),
                coverage: ReturnCoverage::Conditional,
            },
        ];
        let local = states[2].clone();
        let nodes = [ReturnNode::Source, ReturnNode::Context(local)];
        let edges = [
            ReturnEdge::Source,
            ReturnEdge::Coverage,
            ReturnEdge::Call {
                arguments: vec![Ok(BTreeSet::from([1])), Ok(BTreeSet::from([0]))],
                all_parameters: BTreeSet::from([0, 1]),
            },
            ReturnEdge::Call {
                arguments: vec![Err(SummaryBlocker::ExternalSummary)],
                all_parameters: BTreeSet::from([0, 1]),
            },
        ];
        for left in &states {
            for right in &states {
                let mut joined = left.clone();
                joined.join_assign(right);
                assert!(left.leq(&joined) && right.leq(&joined));
                if !left.leq(right) {
                    continue;
                }
                for node in &nodes {
                    assert!(output(node.apply(&ReturnAnalysis, left))
                        .leq(&output(node.apply(&ReturnAnalysis, right))));
                }
                for edge in &edges {
                    assert!(output(edge.apply(&ReturnAnalysis, left))
                        .leq(&output(edge.apply(&ReturnAnalysis, right))));
                }
            }
        }
    }
}
