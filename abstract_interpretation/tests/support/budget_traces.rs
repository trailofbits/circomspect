use std::collections::BTreeSet;

use circomspect_abstract_interpretation::graph::{EdgeId, IndexedGraph, NodeId};
use circomspect_abstract_interpretation::lattice::{Lattice, Set};
use circomspect_abstract_interpretation::solver::{
    solve, Backward, Blocker, Direction, Forward, SolveResult,
};

use crate::{Analysis, Operation};

type StateSlots = (Option<u8>, Option<u8>);
type Outcome = SolveResult<NodeId, EdgeId, Set<u8>, &'static str>;
type Reason = Blocker<NodeId, EdgeId, &'static str>;

const EMPTY: StateSlots = (None, None);

fn assert_snapshot(result: &Outcome, states: &[StateSlots], reasons: &BTreeSet<Reason>) {
    let facts = match result {
        SolveResult::Complete(facts) => {
            assert!(reasons.is_empty(), "unexpected complete result");
            &**facts
        }
        SolveResult::Incomplete { provisional_facts, blockers } => {
            assert!(!reasons.is_empty(), "unexpected incomplete result");
            assert_eq!(blockers, reasons);
            &**provisional_facts
        }
    };
    assert_eq!(facts.len(), states.len());
    for (index, expected) in states.iter().enumerate() {
        let state = &facts[&NodeId::new(index)];
        assert_eq!(state.input, expected.0.map(expected_set), "node {index} input");
        assert_eq!(state.output, expected.1.map(expected_set), "node {index} output");
    }
}

fn expected_set(mask: u8) -> Set<u8> {
    let mut result = Set::bottom();
    for value in [1, 2, 4] {
        if mask & value != 0 {
            result.insert(value);
        }
    }
    result
}

fn check_budgets<D: Direction>(expected: &[([StateSlots; 3], &[usize])]) {
    let graph = IndexedGraph::new(
        vec![Operation::Identity; 3],
        vec![
            (NodeId::new(0), NodeId::new(2), Operation::Add(1)),
            (NodeId::new(0), NodeId::new(1), Operation::Add(2)),
            (NodeId::new(0), NodeId::new(2), Operation::Add(4)),
        ],
        vec![NodeId::new(0)],
        vec![NodeId::new(2), NodeId::new(1)],
    )
    .unwrap();
    for (budget, (states, pending)) in expected.iter().enumerate() {
        let result = solve::<_, _, D>(&graph, &Analysis, Some(budget)).unwrap();
        let blockers = pending.iter().map(|id| Blocker::PendingNode(NodeId::new(*id))).collect();
        assert_snapshot(&result, states, &blockers);
    }
}

#[test]
fn forward_budget_trace_preserves_parallel_edges_and_ordered_queue() {
    check_budgets::<Forward>(&[
        ([EMPTY, EMPTY, EMPTY], &[0]),
        ([(Some(0), None), EMPTY, EMPTY], &[0]),
        ([(Some(0), Some(0)), EMPTY, EMPTY], &[0]),
        ([(Some(0), Some(0)), EMPTY, EMPTY], &[2]),
        ([(Some(0), Some(0)), EMPTY, (Some(1), None)], &[0, 2]),
        ([(Some(0), Some(0)), EMPTY, (Some(1), None)], &[1, 2]),
        ([(Some(0), Some(0)), (Some(2), None), (Some(1), None)], &[0, 1, 2]),
        ([(Some(0), Some(0)), (Some(2), None), (Some(1), None)], &[1, 2]),
        ([(Some(0), Some(0)), (Some(2), None), (Some(5), None)], &[1, 2]),
        ([(Some(0), Some(0)), (Some(2), Some(2)), (Some(5), None)], &[2]),
        ([(Some(0), Some(0)), (Some(2), Some(2)), (Some(5), Some(5))], &[]),
    ]);
}

#[test]
fn backward_budget_trace_preserves_boundary_order_and_natural_slots() {
    check_budgets::<Backward>(&[
        ([EMPTY, EMPTY, EMPTY], &[1, 2]),
        ([EMPTY, EMPTY, (None, Some(0))], &[1, 2]),
        ([EMPTY, (None, Some(0)), (None, Some(0))], &[1, 2]),
        ([EMPTY, (Some(0), Some(0)), (None, Some(0))], &[1, 2]),
        ([EMPTY, (Some(0), Some(0)), (None, Some(0))], &[0, 2]),
        ([(None, Some(2)), (Some(0), Some(0)), (None, Some(0))], &[0, 2]),
        ([(Some(2), Some(2)), (Some(0), Some(0)), (None, Some(0))], &[2]),
        ([(Some(2), Some(2)), (Some(0), Some(0)), (Some(0), Some(0))], &[2]),
        ([(Some(2), Some(2)), (Some(0), Some(0)), (Some(0), Some(0))], &[0]),
        ([(Some(2), Some(3)), (Some(0), Some(0)), (Some(0), Some(0))], &[0, 2]),
        ([(Some(2), Some(3)), (Some(0), Some(0)), (Some(0), Some(0))], &[0]),
        ([(Some(2), Some(7)), (Some(0), Some(0)), (Some(0), Some(0))], &[0]),
        ([(Some(7), Some(7)), (Some(0), Some(0)), (Some(0), Some(0))], &[]),
    ]);
}

fn opaque_graph() -> IndexedGraph<Operation, Operation> {
    IndexedGraph::new(
        vec![Operation::Opaque, Operation::Identity],
        vec![(NodeId::new(0), NodeId::new(1), Operation::Opaque)],
        vec![NodeId::new(0)],
        vec![NodeId::new(1)],
    )
    .unwrap()
}

#[test]
fn forward_opacity_is_recorded_before_the_exhausted_join() {
    let node = Blocker::OpaqueNode { node: NodeId::new(0), reason: "unsupported" };
    let edge = Blocker::OpaqueEdge { edge: EdgeId::new(0), reason: "unsupported" };
    let pending = |id| Blocker::PendingNode(NodeId::new(id));
    let expected = [
        ([EMPTY, EMPTY], BTreeSet::from([pending(0)])),
        ([(Some(0), None), EMPTY], BTreeSet::from([node.clone(), pending(0)])),
        ([(Some(0), Some(0)), EMPTY], BTreeSet::from([node.clone(), edge.clone(), pending(0)])),
        ([(Some(0), Some(0)), EMPTY], BTreeSet::from([node.clone(), edge.clone(), pending(1)])),
        (
            [(Some(0), Some(0)), (Some(0), None)],
            BTreeSet::from([node.clone(), edge.clone(), pending(1)]),
        ),
        ([(Some(0), Some(0)); 2], BTreeSet::from([node, edge])),
    ];
    for (budget, (states, blockers)) in expected.into_iter().enumerate() {
        let result = solve::<_, _, Forward>(&opaque_graph(), &Analysis, Some(budget)).unwrap();
        assert_snapshot(&result, &states, &blockers);
    }
}

#[test]
fn backward_opacity_is_recorded_before_the_exhausted_join() {
    let node = Blocker::OpaqueNode { node: NodeId::new(0), reason: "unsupported" };
    let edge = Blocker::OpaqueEdge { edge: EdgeId::new(0), reason: "unsupported" };
    let pending = |id| Blocker::PendingNode(NodeId::new(id));
    let expected = [
        ([EMPTY, EMPTY], BTreeSet::from([pending(1)])),
        ([EMPTY, (None, Some(0))], BTreeSet::from([pending(1)])),
        ([EMPTY, (Some(0), Some(0))], BTreeSet::from([edge.clone(), pending(1)])),
        ([EMPTY, (Some(0), Some(0))], BTreeSet::from([edge.clone(), pending(0)])),
        (
            [(None, Some(0)), (Some(0), Some(0))],
            BTreeSet::from([node.clone(), edge.clone(), pending(0)]),
        ),
        ([(Some(0), Some(0)); 2], BTreeSet::from([node, edge])),
    ];
    for (budget, (states, blockers)) in expected.into_iter().enumerate() {
        let result = solve::<_, _, Backward>(&opaque_graph(), &Analysis, Some(budget)).unwrap();
        assert_snapshot(&result, &states, &blockers);
    }
}
