// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use circomspect_abstract_interpretation::graph::{IndexedGraph, NodeId};
use circomspect_abstract_interpretation::lattice::{Constant, Lattice, Reachability, Set};
use circomspect_abstract_interpretation::solver::{
    solve, Backward, DataflowAnalysis, Forward, SolveResult, Transfer, TransferOutcome,
};
use proptest::prelude::*;

fn set(bits: u8) -> Set<u8> {
    let mut result = Set::bottom();
    for value in 0..4 {
        if bits & (1 << value) != 0 {
            result.insert(value);
        }
    }
    result
}

fn joined<S: Lattice>(left: &S, right: &S) -> S {
    let mut result = left.clone();
    let changed = result.join_assign(right);
    assert_eq!(changed, &result != left);
    result
}

fn laws<S: Lattice + std::fmt::Debug>(a: &S, b: &S, c: &S) {
    assert!(S::bottom().leq(a));
    assert!(a.leq(a));
    assert_eq!(&joined(a, a), a);
    assert_eq!(joined(a, b), joined(b, a));
    assert_eq!(joined(&joined(a, b), c), joined(a, &joined(b, c)));
    let union = joined(a, b);
    assert!(a.leq(&union) && b.leq(&union));
    if a.leq(b) {
        assert_eq!(&union, b);
    }
}

fn constant(code: u8) -> Constant<u8> {
    match code % 4 {
        0 => Constant::Bottom,
        1 => Constant::Value(0),
        2 => Constant::Value(1),
        _ => Constant::Top,
    }
}

#[test]
fn shared_lattices_preserve_join_laws_and_prior_snapshots() {
    for a in 0..4 {
        for b in 0..4 {
            for c in 0..4 {
                laws(&Arc::new(constant(a)), &Arc::new(constant(b)), &Arc::new(constant(c)));
                laws(&Arc::new(set(a)), &Arc::new(set(b)), &Arc::new(set(c)));
            }
        }
    }
    let original = Arc::new(set(1));
    let mut branch = original.clone();
    assert!(branch.join_assign(&Arc::new(set(2))));
    assert_eq!(*original, set(1));
    assert_eq!(*branch, set(3));
    Arc::make_mut(&mut branch).insert(3);
    assert_eq!(*original, set(1));
    assert_eq!(*branch, set(11));
}

#[test]
fn shared_lattice_order_does_not_traverse_an_identical_snapshot() {
    static COMPARISONS: AtomicUsize = AtomicUsize::new(0);

    #[derive(Clone, Eq, PartialEq)]
    struct CountedSet(Set<u8>);

    impl Lattice for CountedSet {
        fn bottom() -> Self {
            Self(Set::bottom())
        }

        fn leq(&self, other: &Self) -> bool {
            COMPARISONS.fetch_add(1, Ordering::Relaxed);
            self.0.leq(&other.0)
        }

        fn join_assign(&mut self, other: &Self) -> bool {
            self.0.join_assign(&other.0)
        }
    }

    let original = Arc::new(CountedSet(set(1)));
    let mut branch = original.clone();
    assert!(branch.leq(&original));
    assert!(!branch.join_assign(&original));
    assert_eq!(COMPARISONS.load(Ordering::Relaxed), 0);

    let distinct = Arc::new(CountedSet(set(2)));
    assert!(!branch.leq(&distinct));
    assert_eq!(COMPARISONS.load(Ordering::Relaxed), 1);
    assert!(branch.join_assign(&distinct));
    assert_eq!(branch.0, set(3));
    assert_eq!(original.0, set(1));
    assert_eq!(distinct.0, set(2));
}

#[derive(Clone)]
struct Add(u8);

struct Analysis;

impl DataflowAnalysis<IndexedGraph<Add, Add>> for Analysis {
    type State = Set<u8>;
    type Reason = ();

    fn boundary(&self, _: NodeId) -> Self::State {
        Set::bottom()
    }
}

impl Transfer<Analysis, Set<u8>, ()> for Add {
    fn apply(&self, _: &Analysis, input: &Set<u8>) -> TransferOutcome<Set<u8>, ()> {
        let mut output = input.clone();
        output.insert(self.0);
        TransferOutcome::Known(output)
    }
}

fn update(target: &mut Option<BTreeSet<u8>>, values: &BTreeSet<u8>) -> bool {
    let Some(current) = target else {
        *target = Some(values.clone());
        return true;
    };
    let before = current.len();
    current.extend(values);
    current.len() != before
}

type ReferenceFact = (Option<BTreeSet<u8>>, Option<BTreeSet<u8>>);
type ReferenceFacts = BTreeMap<NodeId, ReferenceFact>;

fn reference(nodes: &[u8], edges: &[(usize, usize, u8)], backwards: bool) -> ReferenceFacts {
    let mut facts: BTreeMap<_, _> =
        (0..nodes.len()).map(|i| (NodeId::new(i), (None, None))).collect();
    let boundary = if backwards { nodes.len() - 1 } else { 0 };
    let slot = facts.get_mut(&NodeId::new(boundary)).expect("valid reference node");
    if backwards {
        slot.1 = Some(BTreeSet::new());
    } else {
        slot.0 = Some(BTreeSet::new());
    }
    for _ in 0..100 {
        let mut changed = false;
        for (index, value) in nodes.iter().enumerate() {
            let id = NodeId::new(index);
            let (input, output) = facts.get(&id).expect("valid reference node").clone();
            let source = if backwards { output } else { input };
            let Some(mut source) = source else {
                continue;
            };
            source.insert(*value);
            let slot = facts.get_mut(&id).expect("valid reference node");
            changed |=
                if backwards { update(&mut slot.0, &source) } else { update(&mut slot.1, &source) };
            for &(from, to, edge_value) in edges {
                if (if backwards { to } else { from }) != index {
                    continue;
                }
                let mut through_edge = source.clone();
                through_edge.insert(edge_value);
                let next = if backwards { from } else { to };
                let slot = facts.get_mut(&NodeId::new(next)).expect("valid reference endpoint");
                changed |= if backwards {
                    update(&mut slot.1, &through_edge)
                } else {
                    update(&mut slot.0, &through_edge)
                };
            }
        }
        if !changed {
            return facts;
        }
    }
    panic!("finite reference domain did not converge");
}

fn compare(nodes: &[u8], edges: &[(usize, usize, u8)], backwards: bool, reverse_ids: bool) {
    let id_for =
        |index: usize| NodeId::new(if reverse_ids { nodes.len() - 1 - index } else { index });
    let mut payloads = nodes.to_vec();
    if reverse_ids {
        payloads.reverse();
    }
    let graph = IndexedGraph::new(
        payloads.into_iter().map(Add).collect(),
        edges.iter().map(|&(from, to, value)| (id_for(from), id_for(to), Add(value))).collect(),
        vec![id_for(0)],
        vec![id_for(nodes.len() - 1)],
    )
    .expect("generated graph is valid");
    let result = if backwards {
        solve::<_, _, Backward>(&graph, &Analysis, None)
    } else {
        solve::<_, _, Forward>(&graph, &Analysis, None)
    }
    .expect("valid graph");
    let SolveResult::Complete(actual) = result else {
        panic!("finite graph must converge");
    };
    let expected = reference(nodes, edges, backwards);
    for index in 0..nodes.len() {
        let (input, output) = &expected[&NodeId::new(index)];
        let actual = &actual[&id_for(index)];
        assert_eq!(actual.input.as_ref().map(|set| set.iter().copied().collect()), *input);
        assert_eq!(actual.output.as_ref().map(|set| set.iter().copied().collect()), *output);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(96))]

    #[test]
    fn set_laws(a in any::<u8>(), b in any::<u8>(), c in any::<u8>()) {
        laws(&set(a), &set(b), &set(c));
    }

    #[test]
    fn constant_laws(a in any::<u8>(), b in any::<u8>(), c in any::<u8>()) {
        laws(&constant(a), &constant(b), &constant(c));
    }

    #[test]
    fn generated_transfer_is_monotone(a in any::<u8>(), b in any::<u8>(), value in 0u8..4) {
        let lower = set(a & b);
        let upper = set(a | b);
        let operation = Add(value);
        let TransferOutcome::Known(left) = operation.apply(&Analysis, &lower) else {
            panic!("add transfer is total");
        };
        let TransferOutcome::Known(right) = operation.apply(&Analysis, &upper) else {
            panic!("add transfer is total");
        };
        prop_assert!(lower.leq(&upper));
        prop_assert!(left.leq(&right));
    }

    #[test]
    fn cyclic_graphs_match_round_robin(
        node_count in 1usize..6,
        raw_nodes in proptest::collection::vec(0u8..4, 5),
        raw_edges in proptest::collection::vec((0usize..5, 0usize..5, 0u8..4), 0..12),
    ) {
        let nodes = raw_nodes[..node_count].to_vec();
        let edges: Vec<_> = raw_edges.into_iter().map(|(a, b, value)|
            (a % node_count, b % node_count, value)).collect();
        for backwards in [false, true] {
            compare(&nodes, &edges, backwards, false);
            compare(&nodes, &edges, backwards, true);
        }
    }
}

#[test]
fn reachability_laws_are_exhaustive() {
    let values = [Reachability::Unreachable, Reachability::Reachable];
    for a in values {
        for b in values {
            for c in values {
                laws(&a, &b, &c);
            }
        }
    }
}
