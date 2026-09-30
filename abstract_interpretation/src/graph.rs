//! Typed graph IDs and a validated graph adapter for synthetic CFGs.

use std::fmt::Debug;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NodeId(usize);

impl NodeId {
    pub const fn new(index: usize) -> Self {
        Self(index)
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct EdgeId(usize);

impl EdgeId {
    pub const fn new(index: usize) -> Self {
        Self(index)
    }
}

/// A borrowed edge preserves both its identity and its payload.
#[derive(Clone, Copy, Debug)]
pub struct EdgeRef<'a, N, E> {
    pub source: N,
    pub target: N,
    pub payload: &'a E,
}

/// An immutable CFG view. Implementors may use their own typed IDs and IR.
pub trait FlowGraph {
    type NodeId: Copy + Ord + Debug;
    type EdgeId: Copy + Ord + Debug;
    type Node;
    type Edge;

    fn nodes(&self) -> &[Self::NodeId];
    fn edges(&self) -> &[Self::EdgeId];
    fn node(&self, id: Self::NodeId) -> Option<&Self::Node>;
    fn edge(&self, id: Self::EdgeId) -> Option<EdgeRef<'_, Self::NodeId, Self::Edge>>;
    fn entries(&self) -> &[Self::NodeId];
    fn exits(&self) -> &[Self::NodeId];
}

/// Malformed graph metadata is rejected before a transfer is invoked.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GraphError<N, E> {
    DuplicateNode(N),
    DuplicateEdge(E),
    MissingNode(N),
    MissingEdge(E),
    MissingEndpoint { edge: E, node: N },
    MissingBoundary(N),
}

/// A simple graph with IDs fixed by insertion order.
pub struct IndexedGraph<N, E> {
    node_ids: Vec<NodeId>,
    edge_ids: Vec<EdgeId>,
    nodes: Vec<N>,
    edges: Vec<(NodeId, NodeId, E)>,
    entries: Vec<NodeId>,
    exits: Vec<NodeId>,
}

impl<N, E> IndexedGraph<N, E> {
    /// Validate every endpoint and boundary before creating a graph.
    pub fn new(
        nodes: Vec<N>,
        edges: Vec<(NodeId, NodeId, E)>,
        entries: Vec<NodeId>,
        exits: Vec<NodeId>,
    ) -> Result<Self, GraphError<NodeId, EdgeId>> {
        let node_ids: Vec<_> = (0..nodes.len()).map(NodeId).collect();
        let edge_ids: Vec<_> = (0..edges.len()).map(EdgeId).collect();
        for (index, (source, target, _)) in edges.iter().enumerate() {
            for node in [source, target] {
                if node.0 >= nodes.len() {
                    return Err(GraphError::MissingEndpoint { edge: EdgeId(index), node: *node });
                }
            }
        }
        for node in entries.iter().chain(&exits) {
            if node.0 >= nodes.len() {
                return Err(GraphError::MissingBoundary(*node));
            }
        }
        Ok(Self { node_ids, edge_ids, nodes, edges, entries, exits })
    }
}

impl<N, E> FlowGraph for IndexedGraph<N, E> {
    type NodeId = NodeId;
    type EdgeId = EdgeId;
    type Node = N;
    type Edge = E;

    fn nodes(&self) -> &[Self::NodeId] {
        &self.node_ids
    }

    fn edges(&self) -> &[Self::EdgeId] {
        &self.edge_ids
    }

    fn node(&self, id: NodeId) -> Option<&N> {
        self.nodes.get(id.0)
    }

    fn edge(&self, id: EdgeId) -> Option<EdgeRef<'_, NodeId, E>> {
        let (source, target, payload) = self.edges.get(id.0)?;
        Some(EdgeRef { source: *source, target: *target, payload })
    }

    fn entries(&self) -> &[NodeId] {
        &self.entries
    }

    fn exits(&self) -> &[NodeId] {
        &self.exits
    }
}
