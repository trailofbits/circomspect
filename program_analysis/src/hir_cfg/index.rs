//! Immutable topology for the owning CFG's reachability queries.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{EdgeId, FlowGraph, NodeId};

#[derive(Clone)]
pub(super) struct TopologyIndex {
    ids: Vec<NodeId>,
    positions: BTreeMap<NodeId, usize>,
    outgoing: Vec<Vec<(EdgeId, usize)>>,
    incoming: Vec<Vec<usize>>,
}

impl TopologyIndex {
    pub(super) fn new<G: FlowGraph<NodeId = NodeId, EdgeId = EdgeId>>(graph: &G) -> Self {
        let ids = graph.nodes().to_vec();
        let positions: BTreeMap<_, _> =
            ids.iter().enumerate().map(|(index, id)| (*id, index)).collect();
        let mut outgoing = vec![Vec::new(); ids.len()];
        let mut incoming = vec![Vec::new(); ids.len()];
        for id in graph.edges() {
            let Some(edge) = graph.edge(*id) else { continue };
            let (Some(&source), Some(&target)) =
                (positions.get(&edge.source), positions.get(&edge.target))
            else {
                continue;
            };
            outgoing[source].push((*id, target));
            incoming[target].push(source);
        }
        Self { ids, positions, outgoing, incoming }
    }

    pub(super) fn reaching_candidates(
        &self,
        targets: &BTreeSet<NodeId>,
        candidates: &BTreeSet<NodeId>,
    ) -> BTreeSet<NodeId> {
        let visited = self.reverse_visited(targets);
        candidates
            .iter()
            .filter(|candidate| {
                targets.contains(candidate)
                    || self.positions.get(candidate).is_some_and(|index| visited[*index])
            })
            .copied()
            .collect()
    }

    fn reverse_visited(&self, targets: &BTreeSet<NodeId>) -> Vec<bool> {
        let mut visited = vec![false; self.ids.len()];
        let mut pending = Vec::new();
        for target in targets {
            if let Some(&index) = self.positions.get(target) {
                visited[index] = true;
                pending.push(index);
            }
        }
        while let Some(node) = pending.pop() {
            abstract_interpretation::timeout::check();
            for &source in &self.incoming[node] {
                if !visited[source] {
                    visited[source] = true;
                    pending.push(source);
                }
            }
        }
        visited
    }

    pub(super) fn reachable_nodes(
        &self,
        start: NodeId,
        capacity: usize,
    ) -> Option<BTreeSet<NodeId>> {
        let Some(&start_index) = self.positions.get(&start) else {
            return (capacity >= 1).then(|| BTreeSet::from([start]));
        };
        let mut visited = vec![false; self.ids.len()];
        let mut pending = vec![start_index];
        let mut count = 0;
        while let Some(node) = pending.pop() {
            abstract_interpretation::timeout::check();
            if visited[node] {
                continue;
            }
            visited[node] = true;
            count += 1;
            if count > capacity {
                return None;
            }
            for (_, target) in &self.outgoing[node] {
                pending.push(*target);
            }
        }
        Some(self.collect_visited(&visited))
    }

    pub(super) fn nodes_reachable_from(&self, starts: &BTreeSet<NodeId>) -> BTreeSet<NodeId> {
        let mut visited = vec![false; self.ids.len()];
        let mut pending = Vec::new();
        for start in starts {
            if let Some(&index) = self.positions.get(start) {
                visited[index] = true;
                pending.push(index);
            }
        }
        while let Some(node) = pending.pop() {
            abstract_interpretation::timeout::check();
            for (_, target) in &self.outgoing[node] {
                if !visited[*target] {
                    visited[*target] = true;
                    pending.push(*target);
                }
            }
        }
        let mut reached = starts.clone();
        reached.extend(self.collect_visited(&visited));
        reached
    }

    pub(super) fn reaches(
        &self,
        start: NodeId,
        targets: &BTreeSet<NodeId>,
        excluded: Option<NodeId>,
        pruned: &BTreeSet<EdgeId>,
    ) -> bool {
        if Some(start) == excluded {
            return false;
        }
        if targets.contains(&start) {
            return true;
        }
        let Some(&start_index) = self.positions.get(&start) else { return false };
        let mut visited = vec![false; self.ids.len()];
        let mut pending = vec![start_index];
        while let Some(node) = pending.pop() {
            abstract_interpretation::timeout::check();
            if Some(self.ids[node]) == excluded || visited[node] {
                continue;
            }
            visited[node] = true;
            if targets.contains(&self.ids[node]) {
                return true;
            }
            for (id, target) in &self.outgoing[node] {
                if !pruned.contains(id) {
                    pending.push(*target);
                }
            }
        }
        false
    }

    fn collect_visited(&self, visited: &[bool]) -> BTreeSet<NodeId> {
        self.ids
            .iter()
            .enumerate()
            .filter_map(|(index, id)| visited[index].then_some(*id))
            .collect()
    }
}

#[cfg(test)]
mod tests;
