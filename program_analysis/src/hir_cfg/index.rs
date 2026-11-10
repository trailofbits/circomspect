//! Immutable topology for the owning CFG's reachability queries.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{EdgeId, FlowGraph, NodeId};

#[derive(Clone)]
pub(super) struct TopologyIndex {
    outgoing: BTreeMap<NodeId, Vec<(EdgeId, NodeId)>>,
    incoming: BTreeMap<NodeId, Vec<NodeId>>,
}

impl TopologyIndex {
    pub(super) fn new<G: FlowGraph<NodeId = NodeId, EdgeId = EdgeId>>(graph: &G) -> Self {
        let mut outgoing: BTreeMap<NodeId, Vec<(EdgeId, NodeId)>> = BTreeMap::new();
        let mut incoming: BTreeMap<NodeId, Vec<NodeId>> = BTreeMap::new();
        for id in graph.edges() {
            if let Some(edge) = graph.edge(*id) {
                outgoing.entry(edge.source).or_default().push((*id, edge.target));
                incoming.entry(edge.target).or_default().push(edge.source);
            }
        }
        Self { outgoing, incoming }
    }

    pub(super) fn nodes_reaching(&self, targets: &BTreeSet<NodeId>) -> BTreeSet<NodeId> {
        let mut reached = targets.clone();
        let mut pending: Vec<_> = targets.iter().copied().collect();
        while let Some(node) = pending.pop() {
            let Some(sources) = self.incoming.get(&node) else { continue };
            for source in sources {
                if reached.insert(*source) {
                    pending.push(*source);
                }
            }
        }
        reached
    }

    pub(super) fn reachable_nodes(
        &self,
        start: NodeId,
        capacity: usize,
    ) -> Option<BTreeSet<NodeId>> {
        let mut reached = BTreeSet::new();
        let mut pending = vec![start];
        while let Some(node) = pending.pop() {
            if !reached.insert(node) {
                continue;
            }
            if reached.len() > capacity {
                return None;
            }
            if let Some(edges) = self.outgoing.get(&node) {
                for (_, target) in edges {
                    pending.push(*target);
                }
            }
        }
        Some(reached)
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
