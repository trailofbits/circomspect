use std::collections::BTreeMap;

use abstract_interpretation::graph::{EdgeId, EdgeRef, FlowGraph, IndexedGraph, NodeId};

use crate::interprocedural::{ProjectAnalysis, SummaryBlocker};

fn check_path(edges: &[(usize, usize)], entry: usize, exit: usize) -> Result<(), SummaryBlocker> {
    let mut graph_edges = Vec::new();
    for (source, target) in edges {
        graph_edges.push((NodeId::new(*source), NodeId::new(*target), ()));
    }
    let entry = NodeId::new(entry);
    let exit = NodeId::new(exit);
    let graph = IndexedGraph::new(vec![(); 4], graph_edges, vec![entry], vec![exit]).unwrap();
    ProjectAnalysis::require_linear_caller_path(&graph, entry, exit)
}

#[test]
fn require_linear_caller_paths_distinguish_branches_cycles_and_missing_successors() {
    assert_eq!(check_path(&[(0, 1), (1, 2)], 0, 2), Ok(()));
    assert_eq!(check_path(&[(0, 1), (1, 2), (2, 0)], 0, 2), Ok(()));
    assert_eq!(check_path(&[(0, 1), (0, 2)], 0, 2), Err(SummaryBlocker::UnsupportedContext));
    assert_eq!(check_path(&[(0, 1), (0, 1)], 0, 1), Err(SummaryBlocker::UnsupportedContext));
    assert_eq!(check_path(&[(0, 1)], 0, 2), Err(SummaryBlocker::ExternalSummary));
    assert_eq!(check_path(&[(0, 1), (1, 0)], 0, 2), Err(SummaryBlocker::UnsupportedContext));
    assert_eq!(check_path(&[(0, 0)], 0, 2), Err(SummaryBlocker::UnsupportedContext));
}

struct ListedEdges {
    ids: Vec<EdgeId>,
    resolved: BTreeMap<EdgeId, (NodeId, NodeId)>,
}

impl ListedEdges {
    fn ordered(order: &[usize]) -> Self {
        let mut ids = Vec::new();
        for id in order {
            ids.push(EdgeId::new(*id));
        }
        Self {
            ids,
            resolved: BTreeMap::from([
                (EdgeId::new(0), (NodeId::new(0), NodeId::new(1))),
                (EdgeId::new(1), (NodeId::new(0), NodeId::new(2))),
            ]),
        }
    }
}

impl FlowGraph for ListedEdges {
    type NodeId = NodeId;
    type EdgeId = EdgeId;
    type Node = ();
    type Edge = ();

    fn nodes(&self) -> &[NodeId] {
        &[]
    }

    fn edges(&self) -> &[EdgeId] {
        &self.ids
    }

    fn node(&self, _: NodeId) -> Option<&()> {
        None
    }

    fn edge(&self, id: EdgeId) -> Option<EdgeRef<'_, NodeId, ()>> {
        let (source, target) = self.resolved.get(&id)?;
        Some(EdgeRef { source: *source, target: *target, payload: &() })
    }

    fn entries(&self) -> &[NodeId] {
        &[]
    }

    fn exits(&self) -> &[NodeId] {
        &[]
    }
}

#[test]
fn malformed_edge_refusals_follow_list_order_and_stop_at_exit() {
    let entry = NodeId::new(0);
    let exit = NodeId::new(2);
    for (order, expected) in [
        (vec![0, 2, 1], Err(SummaryBlocker::ExternalSummary)),
        (vec![0, 1, 2], Err(SummaryBlocker::UnsupportedContext)),
        (vec![2], Err(SummaryBlocker::ExternalSummary)),
        (vec![], Err(SummaryBlocker::ExternalSummary)),
    ] {
        let graph = ListedEdges::ordered(&order);
        assert_eq!(ProjectAnalysis::require_linear_caller_path(&graph, entry, exit), expected);
    }
    let graph = ListedEdges::ordered(&[2, 0, 1]);
    assert_eq!(ProjectAnalysis::require_linear_caller_path(&graph, entry, entry), Ok(()));
}
