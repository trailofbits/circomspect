//! A test-only repeated constructor source that parsed loops cannot currently produce.

use std::collections::BTreeMap;

use abstract_interpretation::graph::{FlowGraph, IndexedGraph};

use crate::hir_cfg::index::TopologyIndex;
use crate::hir_cfg::{CfgNodeKind, DefinitionCfg};

pub(crate) fn repeat_constructor_source(cfg: &DefinitionCfg) -> DefinitionCfg {
    let mut cfg = cfg.clone();
    let mut nodes = Vec::new();
    let mut expressions = Vec::new();
    for id in cfg.nodes() {
        let mut node = cfg.node(*id).unwrap().clone();
        if let CfgNodeKind::Instantiate { value, .. } = &mut node.kind {
            expressions.push(*value);
            if expressions.len() == 2 {
                *value = expressions[0];
            }
        }
        nodes.push(node);
    }
    assert_eq!(expressions.len(), 2);
    assert_ne!(expressions[0], expressions[1]);
    let mut edges = Vec::new();
    for id in cfg.edges() {
        let edge = cfg.edge(*id).unwrap();
        edges.push((edge.source, edge.target, *edge.payload));
    }
    cfg.graph = IndexedGraph::new(nodes, edges, vec![cfg.entry], vec![cfg.exit]).unwrap();
    cfg.topology = TopologyIndex::new(&cfg.graph);
    cfg.evaluations = BTreeMap::new();
    for id in cfg.graph.nodes() {
        if let CfgNodeKind::Evaluate(expression) = cfg.graph.node(*id).unwrap().kind {
            cfg.evaluations.entry(expression).or_default().push(*id);
        }
    }
    cfg
}
