//! Directional fixed-point solver with explicit incomplete results.

use std::collections::{BTreeMap, BTreeSet};
use std::ops::Deref;

use crate::graph::{FlowGraph, GraphError};
use crate::lattice::Lattice;

/// Rule-specific semantics and the fact seeded at every entry or exit.
pub trait DataflowAnalysis<G: FlowGraph> {
    type State: Lattice;
    type Reason: Clone + Ord;

    fn boundary(&self, node: G::NodeId) -> Self::State;
}

/// Every node and edge payload supplies a total, monotone transfer.
pub trait Transfer<A, S, R> {
    fn apply(&self, analysis: &A, input: &S) -> TransferOutcome<S, R>;
}

/// Unknown semantics retain a provisional fact and explain its origin.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TransferOutcome<S, R> {
    Known(S),
    Opaque { provisional: S, reason: R },
}

/// Both fields use natural CFG orientation, even in a backward analysis.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeFacts<S> {
    pub input: Option<S>,
    pub output: Option<S>,
}

impl<S> Default for NodeFacts<S> {
    fn default() -> Self {
        Self { input: None, output: None }
    }
}

type FactMap<N, S> = BTreeMap<N, NodeFacts<S>>;

/// Facts from a completed fixed point. Only the solver can construct this token.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CertifiedFacts<N, S>(FactMap<N, S>);

impl<N, S> Deref for CertifiedFacts<N, S> {
    type Target = FactMap<N, S>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Read-only facts whose dependency closure may still contain blockers.
///
/// ```compile_fail
/// use circomspect_abstract_interpretation::solver::{CertifiedFacts, ProvisionalFacts};
/// fn issue_warning(_: &CertifiedFacts<u8, u8>) {}
/// fn reject(provisional: &ProvisionalFacts<u8, u8>) { issue_warning(provisional); }
/// fn main() {}
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProvisionalFacts<N, S>(FactMap<N, S>);

impl<N, S> Deref for ProvisionalFacts<N, S> {
    type Target = FactMap<N, S>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A dependency that prevents certification of the whole result.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Blocker<N, E, R> {
    PendingNode(N),
    OpaqueNode { node: N, reason: R },
    OpaqueEdge { edge: E, reason: R },
}

/// Only `Complete` can be consumed as certified facts by a warning rule.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SolveResult<N, E, S, R> {
    Complete(CertifiedFacts<N, S>),
    Incomplete { provisional_facts: ProvisionalFacts<N, S>, blockers: BTreeSet<Blocker<N, E, R>> },
}

pub type SolveOutcome<G, A> = Result<
    SolveResult<
        <G as FlowGraph>::NodeId,
        <G as FlowGraph>::EdgeId,
        <A as DataflowAnalysis<G>>::State,
        <A as DataflowAnalysis<G>>::Reason,
    >,
    GraphError<<G as FlowGraph>::NodeId, <G as FlowGraph>::EdgeId>,
>;

pub struct Forward;
pub struct Backward;

mod sealed {
    pub trait Sealed {}
}

impl sealed::Sealed for Forward {}
impl sealed::Sealed for Backward {}

/// Selects boundary and traversal orientation without duplicating the solver.
pub trait Direction: sealed::Sealed {
    fn boundaries<G: FlowGraph>(graph: &G) -> &[G::NodeId];
    fn from<S>(facts: &NodeFacts<S>) -> &Option<S>;
    fn from_mut<S>(facts: &mut NodeFacts<S>) -> &mut Option<S>;
    fn to_mut<S>(facts: &mut NodeFacts<S>) -> &mut Option<S>;
    fn next_edges<N: Copy + Ord, E: Copy + Ord>(graph: &ValidatedGraph<N, E>, node: N) -> &[E];
    fn neighbor<N: Copy>(edge: (N, N)) -> N;
}

impl Direction for Forward {
    fn boundaries<G: FlowGraph>(graph: &G) -> &[G::NodeId] {
        graph.entries()
    }
    fn from<S>(facts: &NodeFacts<S>) -> &Option<S> {
        &facts.input
    }
    fn from_mut<S>(facts: &mut NodeFacts<S>) -> &mut Option<S> {
        &mut facts.input
    }
    fn to_mut<S>(facts: &mut NodeFacts<S>) -> &mut Option<S> {
        &mut facts.output
    }
    fn next_edges<N: Copy + Ord, E: Copy + Ord>(graph: &ValidatedGraph<N, E>, node: N) -> &[E] {
        graph.outgoing.get(&node).map_or(&[], Vec::as_slice)
    }
    fn neighbor<N: Copy>(edge: (N, N)) -> N {
        edge.1
    }
}

impl Direction for Backward {
    fn boundaries<G: FlowGraph>(graph: &G) -> &[G::NodeId] {
        graph.exits()
    }
    fn from<S>(facts: &NodeFacts<S>) -> &Option<S> {
        &facts.output
    }
    fn from_mut<S>(facts: &mut NodeFacts<S>) -> &mut Option<S> {
        &mut facts.output
    }
    fn to_mut<S>(facts: &mut NodeFacts<S>) -> &mut Option<S> {
        &mut facts.input
    }
    fn next_edges<N: Copy + Ord, E: Copy + Ord>(graph: &ValidatedGraph<N, E>, node: N) -> &[E] {
        graph.incoming.get(&node).map_or(&[], Vec::as_slice)
    }
    fn neighbor<N: Copy>(edge: (N, N)) -> N {
        edge.0
    }
}

pub struct ValidatedGraph<N: Copy + Ord, E: Copy + Ord> {
    endpoints: BTreeMap<E, (N, N)>,
    outgoing: BTreeMap<N, Vec<E>>,
    incoming: BTreeMap<N, Vec<E>>,
}

impl<N: Copy + Ord, E: Copy + Ord> ValidatedGraph<N, E> {
    fn new<G: FlowGraph<NodeId = N, EdgeId = E>>(graph: &G) -> Result<Self, GraphError<N, E>> {
        let mut nodes = BTreeSet::new();
        for &node in graph.nodes() {
            if !nodes.insert(node) {
                return Err(GraphError::DuplicateNode(node));
            }
            if graph.node(node).is_none() {
                return Err(GraphError::MissingNode(node));
            }
        }
        for &node in graph.entries().iter().chain(graph.exits()) {
            if !nodes.contains(&node) {
                return Err(GraphError::MissingBoundary(node));
            }
        }
        let mut result = Self {
            endpoints: BTreeMap::new(),
            outgoing: BTreeMap::new(),
            incoming: BTreeMap::new(),
        };
        for &edge in graph.edges() {
            let Some(item) = graph.edge(edge) else {
                return Err(GraphError::MissingEdge(edge));
            };
            if result.endpoints.insert(edge, (item.source, item.target)).is_some() {
                return Err(GraphError::DuplicateEdge(edge));
            }
            for node in [item.source, item.target] {
                if !nodes.contains(&node) {
                    return Err(GraphError::MissingEndpoint { edge, node });
                }
            }
            result.outgoing.entry(item.source).or_default().push(edge);
            result.incoming.entry(item.target).or_default().push(edge);
        }
        for edges in result.outgoing.values_mut().chain(result.incoming.values_mut()) {
            edges.sort_unstable();
        }
        Ok(result)
    }
}

struct Working<N: Copy + Ord, E: Copy + Ord, S: Lattice, R: Clone + Ord> {
    facts: FactMap<N, S>,
    edge_facts: BTreeMap<E, Option<S>>,
    queue: BTreeSet<N>,
    blockers: BTreeSet<Blocker<N, E, R>>,
    updates: usize,
    budget: Option<usize>,
}

impl<N: Copy + Ord, E: Copy + Ord, S: Lattice, R: Clone + Ord> Working<N, E, S, R> {
    fn incomplete(mut self, pending: N) -> SolveResult<N, E, S, R> {
        self.blockers.insert(Blocker::PendingNode(pending));
        for node in self.queue {
            self.blockers.insert(Blocker::PendingNode(node));
        }
        SolveResult::Incomplete {
            provisional_facts: ProvisionalFacts(self.facts),
            blockers: self.blockers,
        }
    }

    fn finish(self) -> SolveResult<N, E, S, R> {
        if self.blockers.is_empty() {
            SolveResult::Complete(CertifiedFacts(self.facts))
        } else {
            SolveResult::Incomplete {
                provisional_facts: ProvisionalFacts(self.facts),
                blockers: self.blockers,
            }
        }
    }
}

fn join_limited<S: Lattice>(
    target: &mut Option<S>,
    value: &S,
    updates: &mut usize,
    budget: Option<usize>,
) -> Result<bool, ()> {
    let changes = match target {
        Some(current) => !value.leq(current),
        None => true,
    };
    if !changes {
        return Ok(false);
    }
    if budget.is_some_and(|limit| *updates >= limit) {
        return Err(());
    }
    match target {
        Some(current) => {
            current.join_assign(value);
        }
        None => {
            *target = Some(value.clone());
        }
    }
    *updates += 1;
    Ok(true)
}

type StepResult<G> = Result<
    Option<<G as FlowGraph>::NodeId>,
    GraphError<<G as FlowGraph>::NodeId, <G as FlowGraph>::EdgeId>,
>;

struct FlowContext<'a, G: FlowGraph, A: DataflowAnalysis<G>> {
    graph: &'a G,
    analysis: &'a A,
    validated: &'a ValidatedGraph<G::NodeId, G::EdgeId>,
}

fn seed<G, A, D>(
    graph: &G,
    analysis: &A,
    work: &mut Working<G::NodeId, G::EdgeId, A::State, A::Reason>,
) -> StepResult<G>
where
    G: FlowGraph,
    A: DataflowAnalysis<G>,
    D: Direction,
{
    work.queue.extend(D::boundaries(graph).iter().copied());
    for &node in D::boundaries(graph) {
        let seed = analysis.boundary(node);
        let Some(facts) = work.facts.get_mut(&node) else {
            return Err(GraphError::MissingBoundary(node));
        };
        let slot = D::from_mut(facts);
        match join_limited(slot, &seed, &mut work.updates, work.budget) {
            Ok(true | false) => {}
            Err(()) => return Ok(Some(node)),
        }
    }
    Ok(None)
}

fn propagate_edge<G, A, D>(
    context: &FlowContext<'_, G, A>,
    work: &mut Working<G::NodeId, G::EdgeId, A::State, A::Reason>,
    edge: G::EdgeId,
    current: G::NodeId,
    input: &A::State,
) -> StepResult<G>
where
    G: FlowGraph,
    A: DataflowAnalysis<G>,
    D: Direction,
    G::Edge: Transfer<A, A::State, A::Reason>,
{
    let Some(item) = context.graph.edge(edge) else {
        return Err(GraphError::MissingEdge(edge));
    };
    let value = match item.payload.apply(context.analysis, input) {
        TransferOutcome::Known(value) => value,
        TransferOutcome::Opaque { provisional, reason } => {
            work.blockers.insert(Blocker::OpaqueEdge { edge, reason });
            provisional
        }
    };
    let slot = work.edge_facts.entry(edge).or_default();
    match join_limited(slot, &value, &mut work.updates, work.budget) {
        Ok(true) => {}
        Ok(false) => return Ok(None),
        Err(()) => return Ok(Some(current)),
    }
    let Some(&endpoints) = context.validated.endpoints.get(&edge) else {
        return Err(GraphError::MissingEdge(edge));
    };
    let target = D::neighbor(endpoints);
    let Some(facts) = work.facts.get_mut(&target) else {
        return Err(GraphError::MissingNode(target));
    };
    let slot = D::from_mut(facts);
    match join_limited(slot, &value, &mut work.updates, work.budget) {
        Ok(true) => {
            work.queue.insert(target);
        }
        Ok(false) => {}
        Err(()) => return Ok(Some(target)),
    }
    Ok(None)
}

fn process_node<G, A, D>(
    context: &FlowContext<'_, G, A>,
    work: &mut Working<G::NodeId, G::EdgeId, A::State, A::Reason>,
    node: G::NodeId,
) -> StepResult<G>
where
    G: FlowGraph,
    A: DataflowAnalysis<G>,
    D: Direction,
    G::Node: Transfer<A, A::State, A::Reason>,
    G::Edge: Transfer<A, A::State, A::Reason>,
{
    let Some(facts) = work.facts.get(&node) else {
        return Err(GraphError::MissingNode(node));
    };
    let Some(input) = D::from(facts).as_ref() else {
        return Ok(None);
    };
    let Some(payload) = context.graph.node(node) else {
        return Err(GraphError::MissingNode(node));
    };
    let value = match payload.apply(context.analysis, input) {
        TransferOutcome::Known(value) => value,
        TransferOutcome::Opaque { provisional, reason } => {
            work.blockers.insert(Blocker::OpaqueNode { node, reason });
            provisional
        }
    };
    let Some(facts) = work.facts.get_mut(&node) else {
        return Err(GraphError::MissingNode(node));
    };
    let slot = D::to_mut(facts);
    match join_limited(slot, &value, &mut work.updates, work.budget) {
        Ok(true) => {}
        Ok(false) => return Ok(None),
        Err(()) => return Ok(Some(node)),
    }
    for &edge in D::next_edges(context.validated, node) {
        if let Some(pending) = propagate_edge::<G, A, D>(context, work, edge, node, &value)? {
            return Ok(Some(pending));
        }
    }
    Ok(None)
}

/// Compute the least fixed point, or return only provisional facts with blockers.
///
/// One update is a strict change to a seeded boundary, node fact, or edge fact.
/// An unbounded run requires a finite-height domain or a sound widening in the
/// analysis transfer. Otherwise, pass an update budget to bound the run.
///
/// # Errors
/// Returns a graph error for missing or duplicate node/edge identities, invalid
/// endpoints, or entry/exit boundaries. Analysis opacity and budget exhaustion
/// instead return an incomplete result with provisional facts and blockers.
pub fn solve<G, A, D>(graph: &G, analysis: &A, budget: Option<usize>) -> SolveOutcome<G, A>
where
    G: FlowGraph,
    A: DataflowAnalysis<G>,
    D: Direction,
    G::Node: Transfer<A, A::State, A::Reason>,
    G::Edge: Transfer<A, A::State, A::Reason>,
{
    let validated = ValidatedGraph::new(graph)?;
    let mut work = Working {
        facts: graph.nodes().iter().copied().map(|node| (node, NodeFacts::default())).collect(),
        edge_facts: BTreeMap::new(),
        queue: BTreeSet::new(),
        blockers: BTreeSet::new(),
        updates: 0,
        budget,
    };
    if let Some(pending) = seed::<G, A, D>(graph, analysis, &mut work)? {
        return Ok(work.incomplete(pending));
    }
    let context = FlowContext { graph, analysis, validated: &validated };
    while let Some(&node) = work.queue.first() {
        work.queue.remove(&node);
        if let Some(pending) = process_node::<G, A, D>(&context, &mut work, node)? {
            return Ok(work.incomplete(pending));
        }
    }
    Ok(work.finish())
}
