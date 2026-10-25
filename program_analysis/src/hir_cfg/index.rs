//! Immutable topology for the owning CFG's boolean reachability queries.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{EdgeId, FlowGraph, NodeId};

#[derive(Clone)]
pub(super) struct TopologyIndex {
    outgoing: BTreeMap<NodeId, Vec<(EdgeId, NodeId)>>,
}

impl TopologyIndex {
    pub(super) fn new<G: FlowGraph<NodeId = NodeId, EdgeId = EdgeId>>(graph: &G) -> Self {
        let mut outgoing: BTreeMap<NodeId, Vec<(EdgeId, NodeId)>> = BTreeMap::new();
        for id in graph.edges() {
            if let Some(edge) = graph.edge(*id) {
                outgoing.entry(edge.source).or_default().push((*id, edge.target));
            }
        }
        Self { outgoing }
    }

    pub(super) fn reaches(
        &self,
        start: NodeId,
        targets: &BTreeSet<NodeId>,
        excluded: Option<NodeId>,
        pruned: &BTreeSet<EdgeId>,
    ) -> bool {
        let mut visited = BTreeSet::new();
        let mut pending = vec![start];
        while let Some(node) = pending.pop() {
            if Some(node) == excluded || !visited.insert(node) {
                continue;
            }
            if targets.contains(&node) {
                return true;
            }
            let Some(edges) = self.outgoing.get(&node) else { continue };
            for (id, target) in edges {
                if !pruned.contains(id) {
                    pending.push(*target);
                }
            }
        }
        false
    }
}

#[cfg(test)]
mod tests;
