//! Constraint provenance and certified local facts over the checked HIR CFG.

mod port_expansion;
pub(crate) use crate::hir_facts::port_expansion::RankOnePortError;

#[cfg(test)]
mod availability_tests;
mod access;
mod access_query;
mod domains;
mod demand;
mod evaluation;
mod field;
mod forward;
mod handles;
mod liveness;
#[cfg(test)]
mod occurrence_tests;
mod purity;
#[cfg(test)]
mod ownership_tests;
mod relations;
mod source_assignment;
#[cfg(test)]
mod topology_tests;
mod use_queries;
mod walk;
mod write_validity;
#[cfg(test)]
mod range_tests;

pub(crate) use crate::hir_facts::field::CurveKey;
pub(crate) use crate::hir_facts::relations::GeneratedInputEquation;
pub(crate) use crate::hir_facts::source_assignment::{DescribeSignalAssignment, SourceSignalAssignment};

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Mutex, OnceLock, PoisonError};

use abstract_interpretation::graph::{EdgeId, FlowGraph, GraphError, NodeId};
use abstract_interpretation::solver::{
    solve, Backward, Blocker, Forward, SolveResult, Transfer, TransferOutcome,
};
use parser::hir::{
    AccessPath, AccessStep, ArrayIndex, CallTarget, DefinitionRef, Effect, ExprId, ExprKind,
    HirProject, SymbolId, SymbolKind,
};
use parser::frontend::{AssignmentOperator, InputAssignmentOperator};

use crate::hir_cfg::{Constraint, CfgNodeKind, DefinitionCfg};
use crate::hir_facts::demand::{DemandAnalysis, DemandState};
use crate::hir_facts::use_queries::ReadScope;
use crate::interprocedural::ContextEvidence;
use crate::scalar_evidence::ScalarExpressionEvidence;
use access::key_for_path;
use abstract_interpretation::lattice::Lattice;
use domains::{DegreeUpper, FieldRange};
use forward::{ForwardAnalysis, ForwardState};
use liveness::{LiveState, LivenessAnalysis};
use crate::hir_facts::purity::ScalarEvaluationSafety;
pub(crate) use walk::VisitAccesses;

pub use access::{AccessKey, AccessKeyStep, IndexKey};
pub use domains::{DegreeUpper as Degree, FieldRange as Range};
pub use crate::hir_facts::demand::{AssignmentDemand, UnobservedAssignment};
pub use field::{FieldContext, FieldValue};
pub use handles::{AccessHandle, AccessHandleError};
pub use crate::hir_facts::relations::{
    BitAmbiguity, BitAmbiguityOutcome, BitDecomposition, BitRepresentation, GeneratedEquation,
    NoBitAmbiguityCertificate, NormalizedEquation, QuadraticPolynomial,
};
pub use crate::hir_facts::write_validity::{BodyWriteStatus, NoRepeatedBodyWrite, RepeatedBodyWrite};
pub(crate) use handles::InstanceRelation;
pub(crate) use crate::hir_facts::relations::{
    generated_models_satisfy, generated_seeds, GeneratedAssignments, GeneratedEquationSites,
    ProofBudget,
};

pub(crate) fn exact_compile_time(
    hir: &HirProject,
    field: &FieldContext,
    expression: ExprId,
) -> Option<FieldValue> {
    forward::eval_expression(hir, field, expression, &BTreeMap::new())
}

/// A reporting fact whose certified constructor is private to the analysis.
///
/// ```compile_fail
/// use circomspect_program_analysis::hir_facts::{Fact, Incidence};
/// let forged = Fact::known(Incidence::Zero);
/// ```
///
/// Local queries issue either the value `T` or the blocker set returned by that query.
/// The wrapper stores no separate scope identity and is not a lattice or a global execution
/// certificate. Consumers follow the query contract and any scope carried by `T`.
/// A certified `None` is different from an unavailable fact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Fact<T>(FactState<T>);

#[derive(Clone, Debug, Eq, PartialEq)]
enum FactState<T> {
    Certified(T),
    Unavailable(BTreeSet<FactBlocker>),
}

impl<T> Fact<T> {
    fn known(value: T) -> Self {
        Self(FactState::Certified(value))
    }

    fn blocked(blockers: BTreeSet<FactBlocker>) -> Self {
        Self(FactState::Unavailable(blockers))
    }

    /// Borrow the complete availability state without discarding certified absence.
    pub(crate) fn as_result(&self) -> Result<&T, &BTreeSet<FactBlocker>> {
        match &self.0 {
            FactState::Certified(value) => Ok(value),
            FactState::Unavailable(blockers) => Err(blockers),
        }
    }

    /// Consume the fact, preserving either its value or its complete blocker set.
    pub(crate) fn into_result(self) -> Result<T, BTreeSet<FactBlocker>> {
        match self.0 {
            FactState::Certified(value) => Ok(value),
            FactState::Unavailable(blockers) => Err(blockers),
        }
    }

    #[must_use]
    pub fn certified(&self) -> Option<&T> {
        match &self.0 {
            FactState::Certified(value) => Some(value),
            FactState::Unavailable(_) => None,
        }
    }

    #[must_use]
    pub fn unavailable(&self) -> Option<&BTreeSet<FactBlocker>> {
        match &self.0 {
            FactState::Certified(_) => None,
            FactState::Unavailable(blockers) => Some(blockers),
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FactBlocker {
    Budget(NodeId),
    OpaqueNode(NodeId, String),
    OpaqueEdge(EdgeId, String),
    ExternalSummary,
    AggregateAccess,
    DeferredShape(ExprId),
    AggregateConstraint(NodeId),
    DeferredControl(NodeId),
    OpaqueExpression(ExprId),
    UnsupportedRelation(NodeId),
    WitnessWrite(NodeId, WitnessWriteIssue),
    SignalRead(NodeId, SignalReadIssue),
    MissingExit,
    ForeignQuery,
    ForeignDefinition,
}

impl From<&Blocker<NodeId, EdgeId, String>> for FactBlocker {
    fn from(blocker: &Blocker<NodeId, EdgeId, String>) -> Self {
        match blocker {
            Blocker::PendingNode(node) => Self::Budget(*node),
            Blocker::OpaqueNode { node, reason } => Self::OpaqueNode(*node, reason.clone()),
            Blocker::OpaqueEdge { edge, reason } => Self::OpaqueEdge(*edge, reason.clone()),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum WitnessWriteIssue {
    PossibleRepeat,
    UnresolvedTarget,
    DefiniteRepeat,
    InputReassignment,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SignalReadIssue {
    NoPriorWrite,
    BranchOnlyWrite,
    UnresolvedPriorWrite,
    UnresolvedAccess,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Incidence {
    Zero,
    May,
    Must,
}

type ForwardResult = SolveResult<NodeId, EdgeId, ForwardState, String>;
type BackwardResult = SolveResult<NodeId, EdgeId, LiveState, String>;
type DemandResult = SolveResult<NodeId, EdgeId, DemandState, String>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AnalysisError {
    ForeignProject,
    ForeignCallResults,
    WrongScalarSeeds,
    InvalidGraph(GraphError<NodeId, EdgeId>),
}

struct AnalysisOptions<'a> {
    values: BTreeMap<SymbolId, FieldValue>,
    calls: Option<Cow<'a, ScalarExpressionEvidence>>,
    budget: Option<usize>,
}

pub(crate) struct OwnedAnalysisOptions {
    pub(crate) values: BTreeMap<SymbolId, FieldValue>,
    pub(crate) calls: ScalarExpressionEvidence,
    pub(crate) budget: Option<usize>,
}

/// Local facts retain the solver result privately so reporting queries cannot
/// accidentally consume provisional states without a closure check.
pub struct AnalysisFacts<'a> {
    hir: &'a HirProject,
    cfg: Cow<'a, DefinitionCfg>,
    field: &'a FieldContext,
    calls: Option<Cow<'a, ScalarExpressionEvidence>>,
    forward: ForwardResult,
    backward: BackwardResult,
    demand: DemandResult,
    scalar_evaluation_safety: ScalarEvaluationSafety,
    specialized_parameters: BTreeSet<SymbolId>,
    resolved_deferred: BTreeSet<NodeId>,
    evidence_binding: Option<ContextEvidence>,
    ranges: Mutex<BTreeMap<ExprId, Fact<FieldRange>>>,
    body_writes: OnceLock<write_validity::BodyWriteResult>,
    deferred_branches: OnceLock<Vec<NodeId>>,
}

/// Compute local facts without external call evidence.
///
/// # Errors
/// Returns an error when the CFG, HIR, or initial analysis state cannot be validated.
pub fn analyze<'a>(
    hir: &'a HirProject,
    cfg: &'a DefinitionCfg,
    field: &'a FieldContext,
    budget: Option<usize>,
) -> Result<AnalysisFacts<'a>, AnalysisError> {
    analyze_seeded(
        hir,
        Cow::Borrowed(cfg),
        field,
        AnalysisOptions { values: BTreeMap::new(), calls: None, budget },
    )
}

#[cfg(test)]
pub(crate) fn analyze_with_scalar_parameters<'a>(
    hir: &'a HirProject,
    cfg: &'a DefinitionCfg,
    field: &'a FieldContext,
    values: BTreeMap<SymbolId, FieldValue>,
    budget: Option<usize>,
) -> Result<AnalysisFacts<'a>, AnalysisError> {
    analyze_seeded(hir, Cow::Borrowed(cfg), field, AnalysisOptions { values, calls: None, budget })
}

pub(crate) fn analyze_owned_with_scalar_calls<'a>(
    hir: &'a HirProject,
    cfg: DefinitionCfg,
    field: &'a FieldContext,
    options: OwnedAnalysisOptions,
) -> Result<AnalysisFacts<'a>, AnalysisError> {
    analyze_seeded(
        hir,
        Cow::Owned(cfg),
        field,
        AnalysisOptions {
            values: options.values,
            calls: Some(Cow::Owned(options.calls)),
            budget: options.budget,
        },
    )
}

fn analyze_seeded<'a>(
    hir: &'a HirProject,
    cfg: Cow<'a, DefinitionCfg>,
    field: &'a FieldContext,
    options: AnalysisOptions<'a>,
) -> Result<AnalysisFacts<'a>, AnalysisError> {
    const DEFAULT_UPDATE_BUDGET: usize = 100_000;
    let owned = match cfg.definition() {
        DefinitionRef::Function(id) => hir.function(id).is_some(),
        DefinitionRef::Template(id) => hir.template(id).is_some(),
        DefinitionRef::Bus(id) => hir.bus(id).is_some(),
    };
    if !owned {
        return Err(AnalysisError::ForeignProject);
    }
    if options
        .calls
        .as_deref()
        .is_some_and(|calls| !calls.belongs_to(hir, cfg.definition(), field.curve()))
    {
        return Err(AnalysisError::ForeignCallResults);
    }
    if cfg.scalar_seeds().is_some_and(|seeds| seeds != &options.values) {
        return Err(AnalysisError::WrongScalarSeeds);
    }
    let budget = Some(options.budget.unwrap_or(DEFAULT_UPDATE_BUDGET));
    let specialized_parameters = options.values.keys().copied().collect();
    let forward = solve::<_, _, Forward>(
        cfg.as_ref(),
        &ForwardAnalysis::with_scalar_parameters_and_calls(
            hir,
            field,
            options.values,
            options.calls.as_deref(),
        ),
        budget,
    )
    .map_err(AnalysisError::InvalidGraph)?;
    let resolved_deferred =
        resolved_deferred_nodes(hir, cfg.as_ref(), field, &forward, options.calls.as_deref());
    let pruned_edges =
        forward_pruned_edges(hir, cfg.as_ref(), field, &forward, options.calls.as_deref());
    let liveness = LivenessAnalysis::new(hir, field, cfg.definition())
        .with_pruned_edges(pruned_edges.clone())
        .with_resolved_deferred(resolved_deferred.clone())
        .with_calls(options.calls.as_deref());
    let backward = solve::<_, _, Backward>(cfg.as_ref(), &liveness, budget)
        .map_err(AnalysisError::InvalidGraph)?;
    let scalar_evaluation_safety = ScalarEvaluationSafety::certify(
        hir,
        cfg.as_ref(),
        field,
        &forward,
        options.calls.as_deref(),
    );
    let demand_analysis = DemandAnalysis::new(hir, field, pruned_edges)
        .with_calls(options.calls.as_deref())
        .with_scalar_evaluation_safety(scalar_evaluation_safety.clone())
        .with_resolved_deferred(resolved_deferred.clone());
    let demand = solve::<_, _, Backward>(cfg.as_ref(), &demand_analysis, budget)
        .map_err(AnalysisError::InvalidGraph)?;
    Ok(AnalysisFacts {
        hir,
        cfg,
        field,
        calls: options.calls,
        forward,
        backward,
        demand,
        scalar_evaluation_safety,
        specialized_parameters,
        resolved_deferred,
        evidence_binding: None,
        ranges: Mutex::new(BTreeMap::new()),
        body_writes: OnceLock::new(),
        deferred_branches: OnceLock::new(),
    })
}

fn resolved_deferred_nodes(
    hir: &HirProject,
    cfg: &DefinitionCfg,
    field: &FieldContext,
    result: &ForwardResult,
    calls: Option<&ScalarExpressionEvidence>,
) -> BTreeSet<NodeId> {
    let SolveResult::Complete(facts) = result else { return BTreeSet::new() };
    let mut resolved = BTreeSet::new();
    for id in cfg.nodes() {
        let Some(CfgNodeKind::DeferredAssignment { target, value, operator }) =
            cfg.node(*id).map(|node| &node.kind)
        else {
            continue;
        };
        if *operator != AssignmentOperator::Assign {
            continue;
        }
        if !deferred_scalar_target(hir, target) {
            continue;
        }
        let Some(variables) =
            facts.get(id).and_then(|item| item.input.as_ref()).and_then(ForwardState::variables)
        else {
            continue;
        };
        if forward::eval_expression_with_calls(hir, field, *value, variables, calls).is_some() {
            resolved.insert(*id);
        }
    }
    resolved
}

pub(crate) fn deferred_scalar_target(hir: &HirProject, target: &AccessPath) -> bool {
    if !target.steps.is_empty() {
        return false;
    }
    hir.symbol(target.terminal).is_some_and(|symbol| {
        symbol.kind == SymbolKind::Variable && symbol.rank == 0 && symbol.shape_checked
    })
}

fn forward_pruned_edges(
    hir: &HirProject,
    cfg: &DefinitionCfg,
    field: &FieldContext,
    result: &ForwardResult,
    calls: Option<&ScalarExpressionEvidence>,
) -> BTreeSet<EdgeId> {
    let SolveResult::Complete(facts) = result else { return BTreeSet::new() };
    let analysis = ForwardAnalysis::with_call_values(hir, field, calls);
    cfg.edges()
        .iter()
        .filter_map(|id| {
            let edge = cfg.edge(*id)?;
            let source = facts.get(&edge.source)?.output.as_ref()?;
            let transfer = edge.payload.apply(&analysis, source);
            let TransferOutcome::Known(ForwardState::Unreachable) = transfer else { return None };
            Some(*id)
        })
        .collect()
}

impl AnalysisFacts<'_> {
    pub(crate) fn exact_call_value(&self, expression: ExprId) -> Option<&FieldValue> {
        self.calls.as_deref().and_then(|calls| calls.call_value(expression))
    }

    pub(crate) fn removable_call(&self, expression: ExprId) -> bool {
        self.calls.as_deref().is_some_and(|calls| calls.removable_call(expression))
    }

    pub(crate) fn refined_context(&self) -> Option<&crate::interprocedural::CallContext> {
        self.calls.as_deref().map(crate::scalar_evidence::ScalarExpressionEvidence::context)
    }

    fn forward_analysis(&self) -> ForwardAnalysis<'_> {
        ForwardAnalysis::with_call_values(self.hir, self.field, self.calls.as_deref())
    }

    fn evaluate(
        &self,
        expression: ExprId,
        variables: &BTreeMap<SymbolId, FieldValue>,
    ) -> Option<FieldValue> {
        self.forward_analysis().evaluate(expression, variables)
    }

    /// The exact control-flow graph solved by this analysis.
    ///
    /// Specialization can change graph topology. Node and edge queries must use
    /// IDs from this graph, rather than a CFG supplied before specialization.
    #[must_use]
    pub fn cfg(&self) -> &DefinitionCfg {
        self.cfg.as_ref()
    }

    /// Prove whether one CFG edge is reachable in this bound analysis context.
    /// A provisional fixed point cannot certify an edge, even if its source was visited.
    pub fn reachable_edge(&self, id: EdgeId) -> Fact<bool> {
        let Some(edge) = self.cfg.edge(id) else {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        let SolveResult::Complete(facts) = &self.forward else {
            return Fact::blocked(self.forward_completion_blockers());
        };
        let Some(source) = facts.get(&edge.source).and_then(|item| item.output.as_ref()) else {
            return Fact::known(false);
        };
        let analysis = self.forward_analysis();
        match edge.payload.apply(&analysis, source) {
            TransferOutcome::Known(state) if state.variables().is_none() => Fact::known(false),
            TransferOutcome::Known(_) => {
                let sites = BTreeSet::from([edge.source, edge.target]);
                let blockers = self.deferred_control_blockers(&sites);
                if blockers.is_empty() {
                    Fact::known(true)
                } else {
                    Fact::blocked(blockers)
                }
            }
            TransferOutcome::Opaque { reason, .. } => {
                Fact::blocked(BTreeSet::from([FactBlocker::OpaqueEdge(id, reason)]))
            }
        }
    }

    fn forward_completion_blockers(&self) -> BTreeSet<FactBlocker> {
        let SolveResult::Incomplete { blockers, .. } = &self.forward else {
            return BTreeSet::new();
        };
        let mut reasons = BTreeSet::new();
        for blocker in blockers {
            reasons.insert(FactBlocker::from(blocker));
        }
        if reasons.is_empty() {
            reasons.insert(FactBlocker::MissingExit);
        }
        reasons
    }

    pub(crate) fn must_execute(&self, node: NodeId) -> Fact<bool> {
        let reachable = self.reachable_node(node);
        let reachable = match reachable.into_result() {
            Ok(value) => value,
            Err(blockers) => return Fact::blocked(blockers),
        };
        if !reachable {
            return Fact::known(false);
        }
        if let SolveResult::Incomplete { .. } = &self.forward {
            return Fact::blocked(BTreeSet::from([FactBlocker::Budget(node)]));
        }
        let exit = self.reachable_node(self.cfg.exit());
        let exit_reachable = match exit.into_result() {
            Ok(value) => value,
            Err(blockers) => return Fact::blocked(blockers),
        };
        if !exit_reachable {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        }
        let pruned = forward_pruned_edges(
            self.hir,
            self.cfg.as_ref(),
            self.field,
            &self.forward,
            self.calls.as_deref(),
        );
        Fact::known(!self.path_bypasses(node, &pruned))
    }

    fn path_bypasses(&self, node: NodeId, pruned: &BTreeSet<EdgeId>) -> bool {
        self.cfg.path_exists(
            self.cfg.entry(),
            &BTreeSet::from([self.cfg.exit()]),
            Some(node),
            pruned,
        )
    }

    pub(crate) fn resolved_deferred_assignment(&self, node: NodeId) -> bool {
        self.resolved_deferred.contains(&node)
    }

    pub(crate) fn bind_evidence(&mut self, evidence: ContextEvidence) {
        self.ranges.get_mut().unwrap_or_else(PoisonError::into_inner).clear();
        self.body_writes = OnceLock::new();
        self.deferred_branches = OnceLock::new();
        self.evidence_binding = Some(evidence);
    }

    pub(crate) fn matches_evidence(&self, evidence: &ContextEvidence) -> bool {
        self.evidence_binding.as_ref() == Some(evidence)
            && self.calls.as_deref().map_or(true, |calls| calls.context() == evidence.context())
    }

    pub(crate) fn reachable_node(&self, node: NodeId) -> Fact<bool> {
        if self.cfg.node(node).is_none() {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        if self.certified_dead_node(node) {
            return Fact::known(false);
        }
        let blockers = self.reachability_blockers(&BTreeSet::from([node]));
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        Fact::known(self.site_state(node).is_some_and(|state| state.variables().is_some()))
    }

    #[must_use]
    pub fn hir(&self) -> &HirProject {
        self.hir
    }

    #[must_use]
    pub fn definition(&self) -> DefinitionRef {
        self.cfg.definition()
    }

    #[must_use]
    pub fn curve(&self) -> &program_structure::utils::constants::Curve {
        self.field.curve()
    }

    /// Whether an expression has a reachable CFG evaluation site.
    pub fn reachable_expression(&self, expression: ExprId) -> Fact<bool> {
        if self.hir.expression(expression).is_none() {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        let sites: BTreeSet<_> = self.cfg.evaluation_sites(expression).iter().copied().collect();
        if sites.is_empty() {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        }
        let blockers = self.reachability_blockers(&sites);
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        let mut reachable = false;
        for id in sites {
            if self.site_state(id).is_some_and(|state| state.variables().is_some()) {
                reachable = true;
            }
        }
        Fact::known(reachable)
    }

    fn reachability_blockers(&self, sites: &BTreeSet<NodeId>) -> BTreeSet<FactBlocker> {
        let mut blockers = self.deferred_control_blockers(sites);
        let SolveResult::Incomplete { blockers: solver, .. } = &self.forward else {
            return blockers;
        };
        for blocker in solver {
            match blocker {
                Blocker::PendingNode(node) if self.can_reach_any(*node, sites) => {
                    blockers.insert(FactBlocker::Budget(*node));
                }
                Blocker::OpaqueNode { node, reason }
                    if !sites.contains(node) && self.can_reach_any(*node, sites) =>
                {
                    blockers.insert(FactBlocker::OpaqueNode(*node, reason.clone()));
                }
                Blocker::OpaqueEdge { edge, reason }
                    if self
                        .cfg
                        .edge(*edge)
                        .is_some_and(|item| self.can_reach_any(item.target, sites)) =>
                {
                    blockers.insert(FactBlocker::OpaqueEdge(*edge, reason.clone()));
                }
                Blocker::PendingNode(_)
                | Blocker::OpaqueNode { .. }
                | Blocker::OpaqueEdge { .. } => {}
            }
        }
        blockers
    }

    /// A compile-time exact value or the full canonical field range.
    ///
    /// Complete query results, including blockers, are memoized only within this
    /// immutable solved snapshot. Reaching the cache limit changes reuse, not evidence.
    pub fn range(&self, expression: ExprId) -> Fact<FieldRange> {
        const MAX_CACHED_RANGES: usize = 4096;
        let cached =
            self.ranges.lock().unwrap_or_else(PoisonError::into_inner).get(&expression).cloned();
        if let Some(cached) = cached {
            return cached;
        }
        let fact = self.compute_range(expression);
        let mut ranges = self.ranges.lock().unwrap_or_else(PoisonError::into_inner);
        if ranges.len() < MAX_CACHED_RANGES {
            ranges.insert(expression, fact.clone());
        }
        fact
    }

    fn compute_range(&self, expression: ExprId) -> Fact<FieldRange> {
        let scalar_blockers = self.scalar_blockers(expression);
        if !scalar_blockers.is_empty() {
            return Fact::blocked(scalar_blockers);
        }
        let mut result = FieldRange::Unreachable;
        let mut observed = false;
        for node in self.cfg.evaluation_sites(expression) {
            let Some(variables) = self.site_state(*node).and_then(ForwardState::variables) else {
                continue;
            };
            observed = true;
            let value = self
                .evaluate(expression, variables)
                .map_or(FieldRange::Canonical, FieldRange::Exact);
            result.join_assign(&value);
        }
        if !observed {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        }
        let blockers = self.expression_blockers(expression);
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        Fact::known(result)
    }

    /// Upper bound on witness polynomial degree; unknown operations are unbounded.
    pub fn degree(&self, expression: ExprId) -> Fact<DegreeUpper> {
        let mut blockers = self.expression_blockers(expression);
        blockers.extend(self.scalar_blockers(expression));
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        let analysis = self.forward_analysis();
        let mut result = DegreeUpper::Unreachable;
        let mut observed = false;
        for id in self.cfg.evaluation_sites(expression) {
            let Some(state) = self.site_state(*id) else { continue };
            let (Some(values), Some(degrees)) = (state.variables(), state.degrees()) else {
                continue;
            };
            observed = true;
            result.join_assign(&forward::expression_degree(&analysis, expression, values, degrees));
        }
        if !observed {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        }
        Fact::known(result)
    }

    /// May-dependencies of a source expression, including local variable assignments.
    pub fn dependencies(&self, expression: ExprId) -> Fact<BTreeSet<AccessKey>> {
        let blockers = self.expression_blockers(expression);
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        let mut result = BTreeSet::new();
        let mut observed = false;
        let analysis = self.forward_analysis();
        for id in self.cfg.evaluation_sites(expression) {
            let Some(state) = self.site_state(*id) else { continue };
            let (Some(values), Some(variables)) = (state.variables(), state.dependencies()) else {
                continue;
            };
            observed = true;
            let Some(dependencies) =
                forward::expression_dependencies(&analysis, expression, values, variables)
            else {
                return Fact::blocked(BTreeSet::from([FactBlocker::OpaqueExpression(expression)]));
            };
            result.extend(dependencies);
        }
        if !observed {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        }
        Fact::known(result)
    }

    fn expression_blockers(&self, expression: ExprId) -> BTreeSet<FactBlocker> {
        let mut blockers = BTreeSet::new();
        let mut uses = Vec::new();
        if !expression.visit_accesses_with(
            self.hir,
            &|call| self.exact_call_value(call).is_some(),
            &mut |path| uses.push(path.clone()),
        ) {
            blockers.insert(FactBlocker::OpaqueExpression(expression));
        }
        let mut sites: BTreeSet<_> =
            self.cfg.evaluation_sites(expression).iter().copied().collect();
        let mut seen = BTreeSet::new();
        for path in &uses {
            if self
                .hir
                .symbol(path.root)
                .is_some_and(|symbol| symbol.kind == parser::hir::SymbolKind::Variable)
            {
                self.variable_assignment_sites(path.root, &mut sites, &mut seen);
            }
        }
        blockers.extend(self.deferred_control_blockers(&sites));
        if let SolveResult::Incomplete { blockers: solver_blockers, .. } = &self.forward {
            for blocker in solver_blockers {
                match blocker {
                    Blocker::PendingNode(node) if self.can_reach_any(*node, &sites) => {
                        blockers.insert(FactBlocker::Budget(*node));
                    }
                    Blocker::OpaqueNode { node, reason }
                        if self.can_reach_any(*node, &sites)
                            && uses.iter().any(|path| self.opaque_relevant(*node, path)) =>
                    {
                        blockers.insert(FactBlocker::OpaqueNode(*node, reason.clone()));
                    }
                    Blocker::PendingNode(_) | Blocker::OpaqueNode { .. } => {}
                    Blocker::OpaqueEdge { edge, reason } => {
                        if self
                            .cfg
                            .edge(*edge)
                            .map_or(true, |item| self.can_reach_any(item.target, &sites))
                        {
                            blockers.insert(FactBlocker::OpaqueEdge(*edge, reason.clone()));
                        }
                    }
                }
            }
        }
        blockers
    }

    fn variable_assignment_sites(
        &self,
        variable: parser::hir::SymbolId,
        sites: &mut BTreeSet<NodeId>,
        seen: &mut BTreeSet<parser::hir::SymbolId>,
    ) {
        if !seen.insert(variable) {
            return;
        }
        for id in self.cfg.nodes() {
            let Some(
                CfgNodeKind::Assignment { target, value, .. }
                | CfgNodeKind::DeferredAssignment { target, value, .. },
            ) = self.cfg.node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            if target.root != variable {
                continue;
            }
            sites.insert(*id);
            let mut nested = BTreeSet::new();
            value.visit_accesses(self.hir, &mut |path| {
                if self
                    .hir
                    .symbol(path.root)
                    .is_some_and(|symbol| symbol.kind == parser::hir::SymbolKind::Variable)
                {
                    nested.insert(path.root);
                }
            });
            for child in nested {
                self.variable_assignment_sites(child, sites, seen);
            }
        }
    }

    fn scalar_blockers(&self, expression: ExprId) -> BTreeSet<FactBlocker> {
        let mut blockers = BTreeSet::new();
        let Some(expr) = self.hir.expression(expression) else {
            blockers.insert(FactBlocker::OpaqueExpression(expression));
            return blockers;
        };
        if let ExprKind::Array(_) | ExprKind::Tuple(_) = &expr.kind {
            blockers.insert(FactBlocker::AggregateAccess);
        }
        expression.visit_accesses(self.hir, &mut |path| {
            let index_count = path
                .steps
                .iter()
                .filter(|step| matches!(step, parser::hir::AccessStep::Index { .. }))
                .count();
            if self.hir.symbol(path.terminal).is_some_and(|symbol| {
                symbol.rank > index_count || symbol.kind == parser::hir::SymbolKind::Bus
            }) {
                blockers.insert(FactBlocker::AggregateAccess);
            }
            if self.hir.symbol(path.terminal).is_some_and(|symbol| {
                symbol.value_evidence == parser::hir::ValueEvidence::Deferred
                    && !self.deferred_symbol_resolved(symbol.id)
            }) {
                blockers.insert(FactBlocker::DeferredShape(expression));
            }
        });
        if self.depends_on_parameter(expression, &mut BTreeSet::new()) {
            blockers.insert(FactBlocker::DeferredShape(expression));
        }
        blockers
    }

    fn deferred_symbol_resolved(&self, symbol: SymbolId) -> bool {
        let mut found = false;
        for id in self.cfg.nodes() {
            let Some(node) = self.cfg.node(*id) else { continue };
            let (CfgNodeKind::DeferredAssignment { target, operator, .. }
            | CfgNodeKind::Assignment { target, operator, .. }) = &node.kind
            else {
                continue;
            };
            if target.root != symbol || self.site_state(*id).is_none() {
                continue;
            }
            match &node.kind {
                CfgNodeKind::DeferredAssignment { value, .. } => {
                    found = true;
                    if !self.resolved_deferred.contains(id)
                        && !self.certified_deferred_scalar_site(*id, target, *value, *operator)
                    {
                        return false;
                    }
                }
                CfgNodeKind::Assignment { .. } => {
                    if let Some(origin) = node.origin {
                        if let Some(Effect::OpaqueAssignment { value, .. }) = self
                            .hir
                            .block(origin.block)
                            .and_then(|block| block.effects.get(origin.effect_index))
                        {
                            found = true;
                            if self.exact_call_value(*value).is_none() {
                                return false;
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        found
    }

    fn certified_deferred_scalar_site(
        &self,
        node: NodeId,
        target: &AccessPath,
        value: ExprId,
        operator: AssignmentOperator,
    ) -> bool {
        if operator != AssignmentOperator::Assign || !deferred_scalar_target(self.hir, target) {
            return false;
        }
        let Some(variables) = self.site_state(node).and_then(ForwardState::variables) else {
            return false;
        };
        self.reachable_node(node).certified() == Some(&true)
            && self.evaluate(value, variables).is_some()
            && self.expression_blockers(value).is_empty()
    }

    fn depends_on_parameter(
        &self,
        expression: ExprId,
        seen: &mut BTreeSet<parser::hir::SymbolId>,
    ) -> bool {
        let mut parameter = false;
        let mut variables = BTreeSet::new();
        expression.visit_accesses(self.hir, &mut |path| match self
            .hir
            .symbol(path.root)
            .map(|symbol| symbol.kind)
        {
            Some(parser::hir::SymbolKind::Parameter) => {
                parameter |= !self.specialized_parameters.contains(&path.root);
            }
            Some(parser::hir::SymbolKind::Variable) => {
                variables.insert(path.root);
            }
            Some(
                parser::hir::SymbolKind::Signal
                | parser::hir::SymbolKind::Component
                | parser::hir::SymbolKind::Bus
                | parser::hir::SymbolKind::Tag,
            )
            | None => {}
        });
        for variable in variables {
            if !seen.insert(variable) {
                continue;
            }
            for id in self.cfg.nodes() {
                let Some(
                    CfgNodeKind::Assignment { target, value, operator }
                    | CfgNodeKind::DeferredAssignment { target, value, operator },
                ) = self.cfg.node(*id).map(|node| &node.kind)
                else {
                    continue;
                };
                if target.root == variable && *operator != AssignmentOperator::Assign {
                    return true;
                }
                if target.root == variable && self.depends_on_parameter(*value, seen) {
                    return true;
                }
            }
        }
        parameter
    }

    /// May-liveness immediately before a CFG node.
    pub fn live_before(&self, node: NodeId, path: &AccessPath) -> Fact<bool> {
        let blockers = self.backward_blockers(path);
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        let facts = match &self.backward {
            SolveResult::Complete(facts) => facts.get(&node),
            SolveResult::Incomplete { provisional_facts, .. } => provisional_facts.get(&node),
        };
        let Some(state) = facts.and_then(|facts| facts.input.as_ref()) else {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        };
        let key = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        Fact::known(state.contains_alias(&key).unwrap_or(false))
    }

    /// Whether a schema-backed port is read in this definition's reachable body.
    /// Interprocedural component effects remain unavailable until summarized.
    pub fn read_handle(&self, handle: &AccessHandle) -> Fact<bool> {
        if handle.definition != self.cfg.definition() {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignDefinition]));
        }
        if handle.curve != *self.field.curve() {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        self.read_path(&handle.path, ReadScope::Handle)
    }

    fn backward_blockers(&self, path: &AccessPath) -> BTreeSet<FactBlocker> {
        self.backward_blockers_query(path, false)
    }

    fn backward_blockers_query(
        &self,
        path: &AccessPath,
        schema_checked: bool,
    ) -> BTreeSet<FactBlocker> {
        let mut blockers = self.blockers_for_query(path, schema_checked);
        let SolveResult::Incomplete { blockers: backward, .. } = &self.backward else {
            return blockers;
        };
        for blocker in backward {
            match blocker {
                Blocker::PendingNode(node) => {
                    blockers.insert(FactBlocker::Budget(*node));
                }
                Blocker::OpaqueEdge { edge, reason } => {
                    blockers.insert(FactBlocker::OpaqueEdge(*edge, reason.clone()));
                }
                Blocker::OpaqueNode { node, reason } if self.opaque_relevant(*node, path) => {
                    blockers.insert(FactBlocker::OpaqueNode(*node, reason.clone()));
                }
                Blocker::OpaqueNode { .. } => {}
            }
        }
        blockers
    }

    /// Whether a local access can occur in a generated constraint.
    pub fn incidence(&self, path: &AccessPath) -> Fact<Incidence> {
        self.incidence_query(path, false)
    }

    /// Constraint incidence for a schema-backed port without a source occurrence.
    pub fn incidence_handle(&self, handle: &AccessHandle) -> Fact<Incidence> {
        if handle.definition != self.cfg.definition() {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignDefinition]));
        }
        if handle.curve != *self.field.curve() {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        self.incidence_query(&handle.path, true)
    }

    fn incidence_query(&self, path: &AccessPath, schema_checked: bool) -> Fact<Incidence> {
        let blockers = self.blockers_for_query(path, schema_checked);
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        let query = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        if self.potential_sites(&query).is_empty() {
            return Fact::known(Incidence::Zero);
        }
        let Some(state) = self.exit_state() else {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        };
        let Some((may, _)) = state.constraints() else {
            return Fact::known(Incidence::Zero);
        };
        let must_match = state.must_touches().is_some_and(|keys| keys.contains(&query));
        let may_match = may.iter().any(|site| self.site_touches(*site, &query));
        let value = if must_match {
            Incidence::Must
        } else if may_match {
            Incidence::May
        } else {
            Incidence::Zero
        };
        Fact::known(value)
    }

    /// An exact value proved by a generated equality on every reachable path.
    pub fn constraint_fixed(&self, path: &AccessPath) -> Fact<Option<FieldValue>> {
        self.constraint_fixed_query(path, false)
    }

    /// Fixed value for a schema-backed port without a source occurrence.
    pub fn constraint_fixed_handle(&self, handle: &AccessHandle) -> Fact<Option<FieldValue>> {
        if handle.definition != self.cfg.definition() {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignDefinition]));
        }
        if handle.curve != *self.field.curve() {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        self.constraint_fixed_query(&handle.path, true)
    }

    fn constraint_fixed_query(
        &self,
        path: &AccessPath,
        schema_checked: bool,
    ) -> Fact<Option<FieldValue>> {
        let blockers = self.blockers_for_query(path, schema_checked);
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        let query = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        if self.potential_sites(&query).is_empty() {
            return Fact::known(None);
        }
        let Some(state) = self.exit_state() else {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        };
        let Some(fixed) = state.fixed_equations() else {
            return Fact::known(None);
        };
        let values: BTreeSet<_> = fixed
            .iter()
            .filter_map(|(key, value)| (key == &query).then_some(value.clone()))
            .collect();
        Fact::known((values.len() == 1).then(|| values.into_iter().next()).flatten())
    }

    fn exit_state(&self) -> Option<&ForwardState> {
        let facts = match &self.forward {
            SolveResult::Complete(facts) => facts.get(&self.cfg.exit()),
            SolveResult::Incomplete { provisional_facts, .. } => {
                provisional_facts.get(&self.cfg.exit())
            }
        }?;
        facts.output.as_ref()
    }

    fn site_state(&self, id: NodeId) -> Option<&ForwardState> {
        let facts = match &self.forward {
            SolveResult::Complete(facts) => facts.get(&id),
            SolveResult::Incomplete { provisional_facts, .. } => provisional_facts.get(&id),
        }?;
        facts.input.as_ref()
    }

    pub(crate) fn certified_dead_node(&self, id: NodeId) -> bool {
        // Only a completed fixed point can turn an absent input into a dead-path proof.
        let SolveResult::Complete(facts) = &self.forward else { return false };
        facts
            .get(&id)
            .and_then(|item| item.input.as_ref())
            .and_then(ForwardState::variables)
            .is_none()
    }

    fn site_touches(&self, id: NodeId, query: &AccessKey) -> bool {
        let unknown = ForwardState::boundary();
        let state = self.site_state(id).unwrap_or(&unknown);
        self.site_touches_with_state(id, query, state)
    }

    fn site_touches_with_state(&self, id: NodeId, query: &AccessKey, state: &ForwardState) -> bool {
        let Some(node) = self.cfg.node(id) else { return true };
        let CfgNodeKind::Constraint(constraint) = &node.kind else { return false };
        let empty = BTreeMap::new();
        let variables = state.variables().unwrap_or(&empty);
        let analysis = self.forward_analysis();
        if let Some(touches) = forward::proven_linear_touches(&analysis, &node.kind, variables) {
            return touches.iter().any(|key| key.may_alias(query));
        }
        match constraint {
            Constraint::Assignment { target, value } => {
                let target_touches =
                    key_for_path(self.hir, self.field, target, variables).may_alias(query);
                let index_touches = target.steps.iter().any(|step| match step {
                    AccessStep::Index { index: ArrayIndex::Symbolic(id), .. } => {
                        self.expr_touches(*id, query, state)
                    }
                    AccessStep::Index { index: ArrayIndex::Constant(_), .. }
                    | AccessStep::Port { .. }
                    | AccessStep::Tag { .. } => false,
                });
                target_touches || index_touches || self.expr_touches(*value, query, state)
            }
            Constraint::Equality { left, right } => {
                self.expr_touches(*left, query, state) || self.expr_touches(*right, query, state)
            }
        }
    }

    fn expr_touches(&self, id: ExprId, query: &AccessKey, state: &ForwardState) -> bool {
        let empty_values = BTreeMap::new();
        let values = state.variables().unwrap_or(&empty_values);
        let empty_dependencies = BTreeMap::new();
        let dependencies = state.dependencies().unwrap_or(&empty_dependencies);
        let analysis = self.forward_analysis();
        forward::expression_dependencies(&analysis, id, values, dependencies)
            .map_or(true, |accesses| accesses.iter().any(|key| key.may_alias(query)))
    }

    fn blockers_for_query(&self, path: &AccessPath, schema_checked: bool) -> BTreeSet<FactBlocker> {
        let mut blockers = BTreeSet::new();
        if let Some(blocker) = self.validate_query_path(path, schema_checked) {
            blockers.insert(blocker);
            return blockers;
        }
        let query = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        let potential_sites = self.potential_sites(&query);
        let queried_exit = BTreeSet::from([self.cfg.exit()]);
        blockers.extend(self.deferred_control_blockers(&potential_sites));
        if self.hir.components().iter().any(|item| item.symbol == path.root) {
            blockers.insert(FactBlocker::ExternalSummary);
        }
        if self.hir.symbol(path.terminal).is_some_and(|symbol| {
            symbol.rank
                > path
                    .steps
                    .iter()
                    .filter(|step| matches!(step, parser::hir::AccessStep::Index { .. }))
                    .count()
                || symbol.kind == parser::hir::SymbolKind::Bus
        }) {
            blockers.insert(FactBlocker::AggregateAccess);
        }
        if let Some(state) = self.exit_state() {
            if let Some((may, _)) = state.constraints() {
                for site in may {
                    if self.aggregate_site_touches(*site, &query) {
                        blockers.insert(FactBlocker::AggregateConstraint(*site));
                    }
                    if let Some(expression) = self.unresolved_site_dependency(*site) {
                        blockers.insert(FactBlocker::OpaqueExpression(expression));
                    }
                }
            }
        }
        let SolveResult::Incomplete { blockers: solver_blockers, .. } = &self.forward else {
            return blockers;
        };
        for blocker in solver_blockers {
            match blocker {
                Blocker::PendingNode(node)
                    if (!potential_sites.is_empty()
                        && self.can_reach_any(*node, &queried_exit))
                        || self.opaque_constraint_relevant(*node, path)
                            && self.is_opaque_node(*node) =>
                {
                    blockers.insert(FactBlocker::Budget(*node));
                }
                Blocker::OpaqueEdge { edge, reason } => {
                    if self.cfg.edge(*edge).map_or(true, |item| {
                        !potential_sites.is_empty()
                            && self.can_reach_any(item.target, &queried_exit)
                    }) {
                        blockers.insert(FactBlocker::OpaqueEdge(*edge, reason.clone()));
                    }
                }
                Blocker::OpaqueNode { node, reason }
                    if self.opaque_constraint_relevant(*node, path) =>
                {
                    if self.is_function_call_effect(*node) {
                        blockers.insert(FactBlocker::ExternalSummary);
                    } else {
                        blockers.insert(FactBlocker::OpaqueNode(*node, reason.clone()));
                    }
                }
                Blocker::PendingNode(_) | Blocker::OpaqueNode { .. } => {}
            }
        }
        blockers
    }

    fn validate_query_path(&self, path: &AccessPath, schema_checked: bool) -> Option<FactBlocker> {
        if self.hir.symbol(path.root).is_none() || self.hir.symbol(path.terminal).is_none() {
            return Some(FactBlocker::ForeignQuery);
        }
        if !self.cfg.owns_symbol(path.root) {
            return Some(FactBlocker::ForeignDefinition);
        }
        let mut terminal = path.root;
        for step in &path.steps {
            let valid = match step {
                AccessStep::Index { index: ArrayIndex::Constant(value), .. } => {
                    self.field.parse(value).is_some()
                }
                AccessStep::Index { index: ArrayIndex::Symbolic(id), .. } => {
                    self.hir.expression(*id).is_some()
                }
                AccessStep::Port { port, .. } => {
                    if let Some(port) = self.hir.port(*port) {
                        terminal = port.symbol;
                        true
                    } else {
                        false
                    }
                }
                AccessStep::Tag { symbol, .. } => {
                    terminal = *symbol;
                    self.hir.symbol(*symbol).is_some()
                }
            };
            if !valid {
                return Some(FactBlocker::ForeignQuery);
            }
        }
        if terminal != path.terminal || (!schema_checked && !self.cfg.owns_path(path)) {
            return Some(FactBlocker::ForeignQuery);
        }
        None
    }

    fn potential_sites(&self, query: &AccessKey) -> BTreeSet<NodeId> {
        let incomplete = match &self.forward {
            SolveResult::Complete(_) => false,
            SolveResult::Incomplete { .. } => true,
        };
        let unknown = ForwardState::boundary();
        self.cfg
            .nodes()
            .iter()
            .copied()
            .filter(|node| {
                if incomplete {
                    self.site_touches_with_state(*node, query, &unknown)
                } else {
                    self.site_touches(*node, query)
                }
            })
            .collect()
    }

    fn can_reach_any(&self, start: NodeId, targets: &BTreeSet<NodeId>) -> bool {
        self.cfg.path_exists(start, targets, None, &BTreeSet::new())
    }

    fn deferred_control_blockers(&self, sites: &BTreeSet<NodeId>) -> BTreeSet<FactBlocker> {
        let mut blockers = BTreeSet::new();
        for site in sites {
            if self.certified_dead_node(*site) {
                continue;
            }
            if let Some(node) = self.cfg.node(*site) {
                for control in &node.deferred_controls {
                    if !self.certified_dead_node(*control) && !self.specialized_guard(*control) {
                        blockers.insert(FactBlocker::DeferredControl(*control));
                    }
                }
            }
            for branch in self.deferred_branches() {
                if self.certified_dead_node(*branch) {
                    continue;
                }
                let target = BTreeSet::from([*site]);
                if self.can_reach_any(*branch, &target)
                    && self.can_reach_exit_avoiding(*branch, *site)
                    && !self.specialized_guard(*branch)
                {
                    blockers.insert(FactBlocker::DeferredControl(*branch));
                }
            }
        }
        blockers
    }

    fn deferred_branches(&self) -> &[NodeId] {
        self.deferred_branches.get_or_init(|| {
            let mut branches = Vec::new();
            for site in self.cfg.nodes() {
                if let Some(CfgNodeKind::Branch {
                    guard: parser::hir::ControlGuard::DeferredScalar,
                    ..
                }) = self.cfg.node(*site).map(|node| &node.kind)
                {
                    branches.push(*site);
                }
            }
            branches
        })
    }

    fn specialized_guard(&self, branch: NodeId) -> bool {
        let Some(CfgNodeKind::Branch {
            condition,
            guard: parser::hir::ControlGuard::DeferredScalar,
        }) = self.cfg.node(branch).map(|node| &node.kind)
        else {
            return false;
        };
        if !self.scalar_blockers(*condition).is_empty() {
            return false;
        }
        let Some(values) = self.site_state(branch).and_then(ForwardState::variables) else {
            return false;
        };
        self.evaluate(*condition, values).is_some()
    }

    fn can_reach_exit_avoiding(&self, start: NodeId, excluded: NodeId) -> bool {
        self.cfg.path_exists(
            start,
            &BTreeSet::from([self.cfg.exit()]),
            Some(excluded),
            &BTreeSet::new(),
        )
    }

    fn is_opaque_node(&self, id: NodeId) -> bool {
        let Some(node) = self.cfg.node(id) else { return true };
        match &node.kind {
            CfgNodeKind::Opaque(_)
            | CfgNodeKind::OpaqueAssignment { .. }
            | CfgNodeKind::OpaqueEquality { .. }
            | CfgNodeKind::Instantiate { .. } => true,
            CfgNodeKind::Assignment { operator, .. } => *operator != AssignmentOperator::Assign,
            CfgNodeKind::DeferredAssignment { operator, .. } => {
                *operator != AssignmentOperator::Assign || !self.resolved_deferred.contains(&id)
            }
            CfgNodeKind::Evaluate(expr) => {
                self.hir.expression(*expr).map_or(true, |item| match &item.kind {
                    ExprKind::Opaque(_) | ExprKind::AnonymousComponent { .. } => true,
                    ExprKind::Number(_)
                    | ExprKind::Access(_)
                    | ExprKind::Call { .. }
                    | ExprKind::Array(_)
                    | ExprKind::Tuple(_)
                    | ExprKind::Unary { .. }
                    | ExprKind::Binary { .. }
                    | ExprKind::Ternary { .. }
                    | ExprKind::Parallel(_) => false,
                })
            }
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::LoopHeader
            | CfgNodeKind::Branch { .. }
            | CfgNodeKind::Witness { .. }
            | CfgNodeKind::Constraint(_)
            | CfgNodeKind::Update { .. }
            | CfgNodeKind::Declaration { .. }
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Assert { .. }
            | CfgNodeKind::DeferredAssert { .. }
            | CfgNodeKind::Log => false,
        }
    }

    fn is_function_call_effect(&self, node: NodeId) -> bool {
        let Some(node) = self.cfg.node(node) else { return false };
        match &node.kind {
            CfgNodeKind::OpaqueAssignment { value, .. }
            | CfgNodeKind::DeferredAssignment { value, .. } => self.is_function_call(*value),
            CfgNodeKind::OpaqueEquality { left, right, .. } => {
                self.is_function_call(*left) || self.is_function_call(*right)
            }
            _ => false,
        }
    }

    fn is_function_call(&self, id: ExprId) -> bool {
        let Some(expression) = self.hir.expression(id) else { return false };
        if let ExprKind::Call { target: CallTarget::Function(_), .. } = &expression.kind {
            return true;
        }
        false
    }

    fn opaque_constraint_relevant(&self, node: NodeId, path: &AccessPath) -> bool {
        if let Some(CfgNodeKind::OpaqueAssignment {
            target,
            operator: AssignmentOperator::Witness | AssignmentOperator::ReverseWitness,
            ..
        }) = self.cfg.node(node).map(|item| &item.kind)
        {
            let Some(symbol) = self.hir.symbol(target.terminal) else {
                return self.opaque_relevant(node, path);
            };
            if let parser::hir::SymbolKind::Signal | parser::hir::SymbolKind::Bus = symbol.kind {
                if !self.is_function_call_effect(node) {
                    return self.opaque_relevant(node, path);
                }
                return false;
            }
        }
        self.opaque_relevant(node, path)
    }

    fn aggregate_site_touches(&self, site: NodeId, query: &AccessKey) -> bool {
        let Some(node) = self.cfg.node(site) else { return true };
        let CfgNodeKind::Constraint(constraint) = &node.kind else { return false };
        let empty = BTreeMap::new();
        let variables = self.site_state(site).and_then(ForwardState::variables).unwrap_or(&empty);
        let aggregate = |path: &AccessPath| {
            let key = key_for_path(self.hir, self.field, path, variables);
            key.steps.len() < query.steps.len() && key.may_alias(query)
        };
        let mut found = false;
        match constraint {
            Constraint::Assignment { target, value } => {
                if aggregate(target) {
                    return true;
                }
                value.visit_accesses(self.hir, &mut |path| found |= aggregate(path));
            }
            Constraint::Equality { left, right } => {
                left.visit_accesses(self.hir, &mut |path| found |= aggregate(path));
                right.visit_accesses(self.hir, &mut |path| found |= aggregate(path));
            }
        }
        found
    }

    fn unresolved_site_dependency(&self, site: NodeId) -> Option<ExprId> {
        let node = self.cfg.node(site)?;
        let CfgNodeKind::Constraint(constraint) = &node.kind else { return None };
        let state = self.site_state(site)?;
        let values = state.variables()?;
        let dependencies = state.dependencies()?;
        let analysis = self.forward_analysis();
        let unresolved =
            |id| forward::expression_dependencies(&analysis, id, values, dependencies).is_none();
        match constraint {
            Constraint::Assignment { target, value } => {
                for step in &target.steps {
                    if let AccessStep::Index { index: ArrayIndex::Symbolic(id), .. } = step {
                        if unresolved(*id) {
                            return Some(*id);
                        }
                    }
                }
                unresolved(*value).then_some(*value)
            }
            Constraint::Equality { left, right } => {
                if unresolved(*left) {
                    return Some(*left);
                }
                unresolved(*right).then_some(*right)
            }
        }
    }

    fn opaque_relevant(&self, node_id: NodeId, path: &AccessPath) -> bool {
        let Some(node) = self.cfg.node(node_id) else { return true };
        if let CfgNodeKind::Evaluate(id) = &node.kind {
            if let Some(ExprKind::AnonymousComponent { .. }) =
                self.hir.expression(*id).map(|expression| &expression.kind)
            {
                return self.anonymous_constraint_input_relevant(*id, path);
            }
        }
        if let CfgNodeKind::OpaqueAssignment { target, value, .. }
        | CfgNodeKind::DeferredAssignment { target, value, .. } = &node.kind
        {
            let query = key_for_path(self.hir, self.field, path, &BTreeMap::new());
            let mut relevant = false;
            target.visit_accesses(self.hir, &mut |used| {
                relevant |=
                    key_for_path(self.hir, self.field, used, &BTreeMap::new()).may_alias(&query);
            });
            value.visit_accesses(self.hir, &mut |used| {
                relevant |=
                    key_for_path(self.hir, self.field, used, &BTreeMap::new()).may_alias(&query);
            });
            return relevant;
        }
        if let CfgNodeKind::OpaqueEquality { left, right, .. } = &node.kind {
            let query = key_for_path(self.hir, self.field, path, &BTreeMap::new());
            let mut relevant = false;
            left.visit_accesses(self.hir, &mut |used| {
                relevant |=
                    key_for_path(self.hir, self.field, used, &BTreeMap::new()).may_alias(&query);
            });
            right.visit_accesses(self.hir, &mut |used| {
                relevant |=
                    key_for_path(self.hir, self.field, used, &BTreeMap::new()).may_alias(&query);
            });
            return relevant;
        }
        if let CfgNodeKind::Opaque(_) = &node.kind {
            return true;
        }
        let Some(origin) = node.origin else { return true };
        let Some(effect) =
            self.hir.block(origin.block).and_then(|block| block.effects.get(origin.effect_index))
        else {
            return true;
        };
        match effect {
            parser::hir::Effect::WitnessAssignment { target, .. }
            | parser::hir::Effect::ComponentInstantiation { target, .. } => {
                target.root == path.root
            }
            parser::hir::Effect::Declaration { .. }
            | parser::hir::Effect::OpaqueAssignment { .. }
            | parser::hir::Effect::OpaqueEquality { .. }
            | parser::hir::Effect::ConstraintAssignment { .. }
            | parser::hir::Effect::EqualityConstraint { .. }
            | parser::hir::Effect::VariableAssignment { .. }
            | parser::hir::Effect::DeferredVariableAssignment { .. }
            | parser::hir::Effect::Update { .. }
            | parser::hir::Effect::If { .. }
            | parser::hir::Effect::While { .. }
            | parser::hir::Effect::For { .. }
            | parser::hir::Effect::Return { .. }
            | parser::hir::Effect::Assert { .. }
            | parser::hir::Effect::DeferredAssert { .. }
            | parser::hir::Effect::Log { .. }
            | parser::hir::Effect::AnonymousComponent { .. }
            | parser::hir::Effect::Block(_)
            | parser::hir::Effect::Opaque { .. } => true,
        }
    }

    fn anonymous_constraint_input_relevant(&self, expression: ExprId, path: &AccessPath) -> bool {
        let Some(ExprKind::AnonymousComponent { inputs, .. }) =
            self.hir.expression(expression).map(|item| &item.kind)
        else {
            return false;
        };
        let query = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        for input in inputs {
            if input.operator == InputAssignmentOperator::Witness {
                continue;
            }
            let mut relevant = false;
            let complete = input.value.visit_accesses(self.hir, &mut |used| {
                relevant |=
                    key_for_path(self.hir, self.field, used, &BTreeMap::new()).may_alias(&query);
            });
            if relevant || !complete {
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod call_shape_tests {
    use std::collections::BTreeMap;
    use std::fs;

    use abstract_interpretation::graph::FlowGraph;
    use parser::hir::{lift_project, DefinitionRef, Effect, ExprKind, HirProject};
    use parser::frontend::{AssignmentOperator, load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::{build_cfg, CfgNodeKind};
    use crate::hir_facts::{analyze_with_scalar_parameters, FieldContext, Range};

    fn fixture(source: &str) -> HirProject {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-deferred-prefix-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("case.circom");
        fs::write(&path, source).unwrap();
        let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        lift_project(&loaded).hir
    }

    #[test]
    fn pending_alternative_or_backedge_cannot_certify_a_provisional_deferred_value() {
        for source in [
            "function F(n){var x=n;if(1<<513){x=2;}else{x=3;}return x;}",
            "function F(n){var x=n;for(var i=0;i<17;i++){x=2;}return x;}",
        ] {
            let hir = fixture(source);
            let DefinitionRef::Function(id) = hir.definition("F").unwrap() else { panic!("F") };
            let function = hir.function(id).unwrap();
            let block = hir.block(function.body).unwrap();
            let Some(Effect::Return { value, .. }) = block.effects.last() else { panic!("return") };
            let cfg = build_cfg(&hir, DefinitionRef::Function(id)).unwrap();
            let field = FieldContext::for_curve(Curve::Bn254);
            let seven = field.canonical(7.into());
            let seeds = BTreeMap::from([(function.parameters[0], seven.clone())]);
            for budget in 0..cfg.nodes().len() * 5 {
                let facts =
                    analyze_with_scalar_parameters(&hir, &cfg, &field, seeds.clone(), Some(budget))
                        .unwrap();
                assert_ne!(facts.range(*value).certified(), Some(&Range::Exact(seven.clone())));
            }
        }
    }

    #[test]
    fn a_proved_scalar_prefix_survives_an_unrelated_later_opaque_call() {
        let hir = fixture("function F(n){var x=n;var y=x;var z=Missing();return y;}");
        let DefinitionRef::Function(id) = hir.definition("F").unwrap() else { panic!("F") };
        let function = hir.function(id).unwrap();
        let access = hir
            .expressions()
            .iter()
            .find_map(|expr| {
                let ExprKind::Access(path) = &expr.kind else { return None };
                hir.symbol(path.root).is_some_and(|symbol| symbol.name == "x").then_some(expr.id)
            })
            .unwrap();
        let cfg = build_cfg(&hir, DefinitionRef::Function(id)).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let seven = field.canonical(7.into());
        let seeds = BTreeMap::from([(function.parameters[0], seven.clone())]);
        let facts = analyze_with_scalar_parameters(&hir, &cfg, &field, seeds, None).unwrap();
        assert_eq!(facts.range(access).certified(), Some(&Range::Exact(seven)));
    }

    #[test]
    fn indexed_or_compound_deferred_write_cannot_discharge_scalar_shape() {
        let cases = [
            ("function F(n){var x[1];x[0]=n;return x[0];}", true),
            ("function F(n){var x=0;x+=n;return x;}", false),
        ];
        for (source, indexed) in cases {
            let hir = fixture(source);
            let DefinitionRef::Function(id) = hir.definition("F").unwrap() else { panic!("F") };
            let function = hir.function(id).unwrap();
            let cfg = build_cfg(&hir, DefinitionRef::Function(id)).unwrap();
            let field = FieldContext::for_curve(Curve::Bn254);
            let seeds = BTreeMap::from([(function.parameters[0], field.canonical(7.into()))]);
            let facts = analyze_with_scalar_parameters(&hir, &cfg, &field, seeds, None).unwrap();
            let mut observed = false;
            for node in cfg.nodes() {
                let Some(CfgNodeKind::DeferredAssignment { target, value, operator }) =
                    cfg.node(*node).map(|item| &item.kind)
                else {
                    continue;
                };
                if indexed == target.steps.is_empty() {
                    continue;
                }
                if !indexed && *operator != AssignmentOperator::Add {
                    continue;
                }
                observed = true;
                assert!(!facts.certified_deferred_scalar_site(*node, target, *value, *operator));
            }
            assert!(observed, "deferred write must remain in the source CFG: {source}");
        }
    }
}
