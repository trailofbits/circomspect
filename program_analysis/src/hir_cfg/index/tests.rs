use std::collections::BTreeSet;

use abstract_interpretation::graph::{EdgeId, FlowGraph, IndexedGraph, NodeId};

use crate::hir_cfg::index::TopologyIndex;

fn reference_reaches(
    graph: &IndexedGraph<(), ()>,
    start: NodeId,
    targets: &BTreeSet<NodeId>,
    excluded: Option<NodeId>,
    pruned: &BTreeSet<EdgeId>,
) -> bool {
    let mut reached = BTreeSet::from([start]);
    if let Some(excluded) = excluded {
        reached.remove(&excluded);
    }
    loop {
        let mut changed = false;
        for id in graph.edges() {
            let edge = graph.edge(*id).unwrap();
            if reached.contains(&edge.source)
                && Some(edge.target) != excluded
                && !pruned.contains(id)
            {
                changed |= reached.insert(edge.target);
            }
        }
        if !changed {
            return !reached.is_disjoint(targets);
        }
    }
}

fn target_sets(nodes: &[NodeId]) -> Vec<BTreeSet<NodeId>> {
    let mut sets = Vec::new();
    for mask in 0..1 << nodes.len() {
        let mut selected = BTreeSet::new();
        for (bit, node) in nodes.iter().enumerate() {
            if mask & (1 << bit) != 0 {
                selected.insert(*node);
            }
        }
        sets.push(selected);
    }
    sets
}

fn pruned_sets(edges: &[EdgeId]) -> Vec<BTreeSet<EdgeId>> {
    let mut sets = Vec::new();
    for mask in 0..1 << edges.len() {
        let mut selected = BTreeSet::new();
        for (bit, edge) in edges.iter().enumerate() {
            if mask & (1 << bit) != 0 {
                selected.insert(*edge);
            }
        }
        sets.push(selected);
    }
    sets
}

#[test]
fn indexed_walk_matches_reference_for_all_small_graph_walk_policies() {
    let mut edges = Vec::new();
    for (source, target) in [(0, 1), (0, 1), (1, 2), (2, 1), (0, 3), (3, 2)] {
        edges.push((NodeId::new(source), NodeId::new(target), ()));
    }
    let graph = IndexedGraph::new(vec![(); 4], edges, vec![], vec![]).unwrap();
    let index = TopologyIndex::new(&graph);
    let mut exclusions = vec![None];
    for node in graph.nodes() {
        exclusions.push(Some(*node));
    }
    for start in graph.nodes() {
        for targets in target_sets(graph.nodes()) {
            for excluded in &exclusions {
                for pruned in pruned_sets(graph.edges()) {
                    assert_eq!(
                        index.reaches(*start, &targets, *excluded, &pruned),
                        reference_reaches(&graph, *start, &targets, *excluded, &pruned),
                        "{start:?} -> {targets:?}, excluding {excluded:?}, pruning {pruned:?}",
                    );
                }
            }
        }
    }
}

#[test]
fn target_start_is_reachable_without_metadata_unless_excluded() {
    let graph = IndexedGraph::<(), ()>::new(vec![], vec![], vec![], vec![]).unwrap();
    let index = TopologyIndex::new(&graph);
    let start = NodeId::new(7);
    let targets = BTreeSet::from([start]);
    assert!(index.reaches(start, &targets, None, &BTreeSet::new()));
    assert!(!index.reaches(start, &targets, Some(start), &BTreeSet::new()));
    assert!(!index.reaches(start, &BTreeSet::new(), None, &BTreeSet::new()));
    assert_eq!(index.reaching_candidates(&targets, &targets), targets);
    assert!(index.reaching_candidates(&BTreeSet::new(), &targets).is_empty());
}

#[test]
fn multiple_starts_cover_the_union_of_their_successors() {
    let graph = IndexedGraph::new(
        vec![(); 5],
        vec![
            (NodeId::new(0), NodeId::new(1), ()),
            (NodeId::new(1), NodeId::new(2), ()),
            (NodeId::new(3), NodeId::new(4), ()),
        ],
        vec![],
        vec![],
    )
    .unwrap();
    let starts = BTreeSet::from([NodeId::new(0), NodeId::new(3)]);
    let reached = TopologyIndex::new(&graph).nodes_reachable_from(&starts);
    assert_eq!(reached.len(), 5);
}

#[test]
fn reverse_walk_matches_forward_reference_for_every_three_node_graph() {
    let foreign = NodeId::new(7);
    for mask in 0..1 << 9 {
        let mut edges = Vec::new();
        for source in 0..3 {
            for target in 0..3 {
                if mask & (1 << (source * 3 + target)) != 0 {
                    edges.push((NodeId::new(source), NodeId::new(target), ()));
                }
            }
        }
        let graph = IndexedGraph::new(vec![(); 3], edges, vec![], vec![]).unwrap();
        let index = TopologyIndex::new(&graph);
        let mut nodes = graph.nodes().to_vec();
        nodes.push(foreign);
        for targets in target_sets(&nodes) {
            let candidates: BTreeSet<_> = nodes.iter().copied().collect();
            let reached = index.reaching_candidates(&targets, &candidates);
            let candidates = BTreeSet::from([NodeId::new(0), NodeId::new(2), foreign]);
            assert_eq!(
                index.reaching_candidates(&targets, &candidates),
                reached.intersection(&candidates).copied().collect()
            );
            for start in &nodes {
                assert_eq!(
                    reached.contains(start),
                    reference_reaches(&graph, *start, &targets, None, &BTreeSet::new()),
                    "edges {mask}, {start:?} -> {targets:?}",
                );
            }
        }
    }
}

#[test]
fn reverse_walk_handles_parallel_edges_and_cycles() {
    let mut edges = Vec::new();
    for (source, target) in [(0, 1), (0, 1), (1, 2), (2, 1), (3, 4)] {
        edges.push((NodeId::new(source), NodeId::new(target), ()));
    }
    let graph = IndexedGraph::new(vec![(); 6], edges, vec![], vec![]).unwrap();
    let index = TopologyIndex::new(&graph);
    for targets in target_sets(graph.nodes()) {
        let candidates: BTreeSet<_> = graph.nodes().iter().copied().collect();
        let reached = index.reaching_candidates(&targets, &candidates);
        for start in graph.nodes() {
            assert_eq!(
                reached.contains(start),
                reference_reaches(&graph, *start, &targets, None, &BTreeSet::new()),
            );
        }
    }
}

#[test]
fn bounded_forward_sets_preserve_reachability_or_require_fallback() {
    for mask in 0..1 << 9 {
        let mut edges = Vec::new();
        for source in 0..3 {
            for target in 0..3 {
                if mask & (1 << (source * 3 + target)) != 0 {
                    let edge = (NodeId::new(source), NodeId::new(target), ());
                    edges.extend([edge, edge]);
                }
            }
        }
        let graph = IndexedGraph::new(vec![(); 3], edges, vec![], vec![]).unwrap();
        let index = TopologyIndex::new(&graph);
        let mut nodes = graph.nodes().to_vec();
        nodes.push(NodeId::new(7));
        for start in &nodes {
            let mut expected = BTreeSet::new();
            for target in &nodes {
                if reference_reaches(
                    &graph,
                    *start,
                    &BTreeSet::from([*target]),
                    None,
                    &BTreeSet::new(),
                ) {
                    expected.insert(*target);
                }
            }
            for capacity in 0..=nodes.len() {
                let actual = index.reachable_nodes(*start, capacity);
                if expected.len() <= capacity {
                    assert_eq!(actual.as_ref(), Some(&expected));
                } else {
                    assert!(actual.is_none());
                }
            }
        }
    }
}
