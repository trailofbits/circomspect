// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use std::collections::BTreeSet;

use circomspect_abstract_interpretation::graph::{
    EdgeId, EdgeRef, FlowGraph, GraphError, IndexedGraph, NodeId,
};
use circomspect_abstract_interpretation::lattice::{Lattice, Set};
use circomspect_abstract_interpretation::solver::{
    solve, Backward, Blocker, CertifiedFacts, DataflowAnalysis, Forward, SolveResult, Transfer,
    TransferOutcome,
};

#[derive(Clone)]
enum Operation {
    Identity,
    Add(u8),
    Opaque,
}

struct Analysis;

impl DataflowAnalysis<IndexedGraph<Operation, Operation>> for Analysis {
    type State = Set<u8>;
    type Reason = &'static str;

    fn boundary(&self, _: NodeId) -> Self::State {
        Set::bottom()
    }
}

impl Transfer<Analysis, Set<u8>, &'static str> for Operation {
    fn apply(&self, _: &Analysis, input: &Set<u8>) -> TransferOutcome<Set<u8>, &'static str> {
        match self {
            Self::Identity => TransferOutcome::Known(input.clone()),
            Self::Add(value) => {
                let mut output = input.clone();
                output.insert(*value);
                TransferOutcome::Known(output)
            }
            Self::Opaque => {
                TransferOutcome::Opaque { provisional: input.clone(), reason: "unsupported" }
            }
        }
    }
}

fn values(facts: &CertifiedFacts<NodeId, Set<u8>>, node: usize) -> BTreeSet<u8> {
    facts[&NodeId::new(node)]
        .output
        .as_ref()
        .map_or_else(BTreeSet::new, |set| set.iter().copied().collect())
}

#[test]
fn forward_loop_and_parallel_edges_join_distinct_contributions() {
    let graph = IndexedGraph::new(
        vec![Operation::Identity, Operation::Identity, Operation::Identity],
        vec![
            (NodeId::new(0), NodeId::new(1), Operation::Add(1)),
            (NodeId::new(0), NodeId::new(1), Operation::Add(2)),
            (NodeId::new(1), NodeId::new(1), Operation::Add(3)),
            (NodeId::new(1), NodeId::new(2), Operation::Identity),
        ],
        vec![NodeId::new(0)],
        vec![NodeId::new(2)],
    )
    .expect("valid graph");
    let result = solve::<_, _, Forward>(&graph, &Analysis, None).expect("valid graph");
    let SolveResult::Complete(facts) = result else {
        panic!("expected a fixed point");
    };
    assert_eq!(values(&facts, 2), BTreeSet::from([1, 2, 3]));
}

#[test]
fn backward_flow_seeds_all_exits() {
    let graph = IndexedGraph::new(
        vec![Operation::Identity, Operation::Add(1), Operation::Add(2)],
        vec![
            (NodeId::new(0), NodeId::new(1), Operation::Identity),
            (NodeId::new(0), NodeId::new(2), Operation::Identity),
        ],
        vec![NodeId::new(0)],
        vec![NodeId::new(1), NodeId::new(2)],
    )
    .expect("valid graph");
    let result = solve::<_, _, Backward>(&graph, &Analysis, None).expect("valid graph");
    let SolveResult::Complete(facts) = result else {
        panic!("expected a fixed point");
    };
    assert_eq!(
        facts[&NodeId::new(0)]
            .input
            .as_ref()
            .map(|set| set.iter().copied().collect::<BTreeSet<_>>()),
        Some(BTreeSet::from([1, 2]))
    );
}

#[test]
fn unreachable_opacity_does_not_block_certification() {
    let graph = IndexedGraph::new(
        vec![Operation::Identity, Operation::Opaque],
        vec![],
        vec![NodeId::new(0)],
        vec![NodeId::new(0)],
    )
    .expect("valid graph");
    let result = solve::<_, _, Forward>(&graph, &Analysis, None).expect("valid graph");
    let SolveResult::Complete(facts) = result else {
        panic!("unreachable node must not block");
    };
    assert!(facts[&NodeId::new(1)].input.is_none());
}

#[test]
fn reachable_opacity_and_budget_exhaustion_never_certify() {
    let graph = IndexedGraph::new(
        vec![Operation::Opaque],
        vec![],
        vec![NodeId::new(0)],
        vec![NodeId::new(0)],
    )
    .expect("valid graph");
    let result = solve::<_, _, Forward>(&graph, &Analysis, None).expect("valid graph");
    let SolveResult::Incomplete { blockers, .. } = result else {
        panic!("opacity must block");
    };
    let expected = Blocker::OpaqueNode { node: NodeId::new(0), reason: "unsupported" };
    assert!(blockers.contains(&expected));

    let result = solve::<_, _, Forward>(&graph, &Analysis, Some(0)).expect("valid graph");
    let SolveResult::Incomplete { blockers, provisional_facts } = result else {
        panic!("budget must block");
    };
    assert!(blockers.contains(&Blocker::PendingNode(NodeId::new(0))));
    assert!(provisional_facts[&NodeId::new(0)].input.is_none());
}

#[test]
fn exact_update_budget_can_complete() {
    let graph = IndexedGraph::new(
        vec![Operation::Identity],
        vec![],
        vec![NodeId::new(0)],
        vec![NodeId::new(0)],
    )
    .expect("valid graph");
    let result = solve::<_, _, Forward>(&graph, &Analysis, Some(2)).expect("valid graph");
    let SolveResult::Complete(_) = result else {
        panic!("two strict changes are sufficient");
    };
    let result = solve::<_, _, Forward>(&graph, &Analysis, Some(1)).expect("valid graph");
    let SolveResult::Incomplete { blockers, .. } = result else {
        panic!("one strict change is insufficient");
    };
    assert!(blockers.contains(&Blocker::PendingNode(NodeId::new(0))));
}

#[test]
fn exact_budget_counts_seed_node_edge_and_destination_changes() {
    let graph = IndexedGraph::new(
        vec![Operation::Identity; 2],
        vec![(NodeId::new(0), NodeId::new(1), Operation::Identity)],
        vec![NodeId::new(0)],
        vec![NodeId::new(1)],
    )
    .expect("valid graph");
    let result = solve::<_, _, Forward>(&graph, &Analysis, Some(5)).expect("valid graph");
    let SolveResult::Complete(_) = result else {
        panic!("five strict changes reach the fixed point");
    };
    let result = solve::<_, _, Forward>(&graph, &Analysis, Some(4)).expect("valid graph");
    let SolveResult::Incomplete { blockers, .. } = result else {
        panic!("four strict changes leave the destination pending");
    };
    assert!(blockers.contains(&Blocker::PendingNode(NodeId::new(1))));
}

#[test]
fn exact_budget_allows_remaining_no_change_work() {
    let graph = IndexedGraph::new(
        vec![Operation::Identity],
        vec![(NodeId::new(0), NodeId::new(0), Operation::Identity)],
        vec![NodeId::new(0)],
        vec![NodeId::new(0)],
    )
    .expect("valid graph");
    let result = solve::<_, _, Forward>(&graph, &Analysis, Some(3)).expect("valid graph");
    let SolveResult::Complete(_) = result else {
        panic!("no-change loop traversal must complete at the exact budget");
    };
}

#[test]
fn edge_opacity_records_only_reachable_origins_in_either_direction() {
    let graph = IndexedGraph::new(
        vec![Operation::Identity; 4],
        vec![
            (NodeId::new(0), NodeId::new(1), Operation::Opaque),
            (NodeId::new(2), NodeId::new(3), Operation::Opaque),
        ],
        vec![NodeId::new(0)],
        vec![NodeId::new(1)],
    )
    .expect("valid graph");
    for result in [
        solve::<_, _, Forward>(&graph, &Analysis, None).expect("valid graph"),
        solve::<_, _, Backward>(&graph, &Analysis, None).expect("valid graph"),
    ] {
        let SolveResult::Incomplete { blockers, .. } = result else {
            panic!("reachable edge opacity must block");
        };
        assert!(
            blockers.contains(&Blocker::OpaqueEdge { edge: EdgeId::new(0), reason: "unsupported" })
        );
        assert!(!blockers
            .contains(&Blocker::OpaqueEdge { edge: EdgeId::new(1), reason: "unsupported" }));
    }
}

#[test]
fn invalid_endpoint_is_rejected_before_solving() {
    let result = IndexedGraph::new(
        vec![Operation::Identity],
        vec![(NodeId::new(0), NodeId::new(1), Operation::Opaque)],
        vec![NodeId::new(0)],
        vec![NodeId::new(0)],
    );
    let Err(GraphError::MissingEndpoint { edge, node }) = result else {
        panic!("invalid edge must be rejected by the graph constructor");
    };
    assert_eq!(edge, EdgeId::new(0));
    assert_eq!(node, NodeId::new(1));
}

#[test]
fn zero_budget_reports_every_pending_entry() {
    let graph = IndexedGraph::new(
        vec![Operation::Identity; 2],
        vec![],
        vec![NodeId::new(0), NodeId::new(1)],
        vec![NodeId::new(0)],
    )
    .expect("valid graph");
    let result = solve::<_, _, Forward>(&graph, &Analysis, Some(0)).expect("valid graph");
    let SolveResult::Incomplete { blockers, .. } = result else {
        panic!("no seed update fits a zero budget");
    };
    assert!(blockers.contains(&Blocker::PendingNode(NodeId::new(0))));
    assert!(blockers.contains(&Blocker::PendingNode(NodeId::new(1))));
}

struct InvalidAdapter;

static SINGLE_NODE: [NodeId; 1] = [NodeId::new(0)];
static SINGLE_EDGE: [EdgeId; 1] = [EdgeId::new(0)];

impl FlowGraph for InvalidAdapter {
    type NodeId = NodeId;
    type EdgeId = EdgeId;
    type Node = Operation;
    type Edge = Operation;

    fn nodes(&self) -> &[NodeId] {
        &SINGLE_NODE
    }

    fn edges(&self) -> &[EdgeId] {
        &SINGLE_EDGE
    }

    fn node(&self, _: NodeId) -> Option<&Operation> {
        Some(&Operation::Opaque)
    }

    fn edge(&self, _: EdgeId) -> Option<EdgeRef<'_, NodeId, Operation>> {
        Some(EdgeRef {
            source: NodeId::new(0),
            target: NodeId::new(1),
            payload: &Operation::Opaque,
        })
    }

    fn entries(&self) -> &[NodeId] {
        &SINGLE_NODE
    }

    fn exits(&self) -> &[NodeId] {
        &SINGLE_NODE
    }
}

impl DataflowAnalysis<InvalidAdapter> for Analysis {
    type State = Set<u8>;
    type Reason = &'static str;

    fn boundary(&self, _: NodeId) -> Self::State {
        Set::bottom()
    }
}

#[test]
fn external_adapters_are_validated_before_any_transfer() {
    let result = solve::<_, _, Forward>(&InvalidAdapter, &Analysis, None);
    let Err(GraphError::MissingEndpoint { edge, node }) = result else {
        panic!("malformed adapter must fail before its opaque transfer");
    };
    assert_eq!(edge, EdgeId::new(0));
    assert_eq!(node, NodeId::new(1));
}

#[path = "support/budget_traces.rs"]
mod budget_traces;
