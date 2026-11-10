use std::collections::BTreeSet;
use std::fs;

use abstract_interpretation::graph::{EdgeId, FlowGraph, NodeId};
use abstract_interpretation::solver::{Blocker, SolveResult};
use parser::hir::{lift_project, HirProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::DefinitionCfg;
use crate::hir_facts::{analyze, AnalysisFacts, FactBlocker, FieldContext};

fn fixture(source: &str) -> HirProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-topology-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    fs::create_dir_all(&directory).unwrap();
    let file = directory.join("case.circom");
    fs::write(&file, source).unwrap();
    lift_project(&load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3))))
        .hir
}

fn reference_reaches(
    cfg: &DefinitionCfg,
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
        for id in cfg.edges() {
            let edge = cfg.edge(*id).unwrap();
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

fn compare_raw_queries(facts: &AnalysisFacts<'_>) {
    let cfg = facts.cfg();
    let pruned = BTreeSet::new();
    for start in cfg.nodes() {
        for target in cfg.nodes() {
            let targets = BTreeSet::from([*target]);
            assert_eq!(
                facts.can_reach_any(*start, &targets),
                reference_reaches(cfg, *start, &targets, None, &pruned),
            );
            let targets = BTreeSet::from([cfg.exit()]);
            assert_eq!(
                facts.can_reach_exit_avoiding(*start, *target),
                reference_reaches(cfg, *start, &targets, Some(*target), &pruned),
            );
        }
    }
}

fn compare_bypass_queries(facts: &AnalysisFacts<'_>) {
    let cfg = facts.cfg();
    let mut pruning = vec![BTreeSet::new(), cfg.edges().iter().copied().collect()];
    for edge in cfg.edges() {
        pruning.push(BTreeSet::from([*edge]));
    }
    for pruned in pruning {
        for excluded in cfg.nodes() {
            assert_eq!(
                facts.path_bypasses(*excluded, &pruned),
                reference_reaches(
                    cfg,
                    cfg.entry(),
                    &BTreeSet::from([cfg.exit()]),
                    Some(*excluded),
                    &pruned,
                ),
            );
        }
    }
}

#[test]
fn fact_walk_policies_match_full_edge_reachability() {
    for source in [
        "function Check(n){if(n){return 0;}return 1;}",
        "template Check(){signal input n;if(0){var hidden=7;}while(n){var x=1;}}",
    ] {
        let hir = fixture(source);
        let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("Check").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let facts = analyze(&hir, &cfg, &field, None).unwrap();
        compare_raw_queries(&facts);
        compare_bypass_queries(&facts);
    }
}

fn reference_reachability_blockers(
    facts: &AnalysisFacts<'_>,
    sites: &BTreeSet<NodeId>,
) -> BTreeSet<FactBlocker> {
    let mut result = facts.deferred_control_blockers(sites);
    let SolveResult::Incomplete { blockers, .. } = &facts.forward else { return result };
    let reaches = |node| reference_reaches(facts.cfg(), node, sites, None, &BTreeSet::new());
    for blocker in blockers {
        let relevant = match blocker {
            Blocker::PendingNode(node) => reaches(*node),
            Blocker::OpaqueNode { node, .. } => !sites.contains(node) && reaches(*node),
            Blocker::OpaqueEdge { edge, .. } => {
                facts.cfg().edge(*edge).is_some_and(|item| reaches(item.target))
            }
        };
        if relevant {
            result.insert(FactBlocker::from(blocker));
        }
    }
    result
}

fn include_mixed_solver_blockers(facts: &mut AnalysisFacts<'_>) {
    let mut nodes = facts.cfg().nodes().to_vec();
    let mut edges = facts.cfg().edges().to_vec();
    nodes.push(NodeId::new(usize::MAX));
    edges.push(EdgeId::new(usize::MAX));
    let SolveResult::Incomplete { blockers, .. } = &mut facts.forward else { return };
    for node in nodes {
        blockers.insert(Blocker::PendingNode(node));
        blockers.insert(Blocker::OpaqueNode { node, reason: format!("opaque node {node:?}") });
    }
    for edge in edges {
        blockers.insert(Blocker::OpaqueEdge { edge, reason: format!("opaque edge {edge:?}") });
    }
}

#[test]
fn reachability_blockers_match_forward_paths_at_every_query_site_and_budget() {
    for source in [
        "function Check(n){while(n){n--;if(n){return Missing(n);}}return 1;}",
        "template Check(n){if(n){var x=Missing();}var y=1;}",
        "template Check(){if(0){var hidden=Missing();}var live=3;}",
    ] {
        let hir = fixture(source);
        let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("Check").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        for budget in [Some(0), Some(1), Some(8), None] {
            let mut facts = analyze(&hir, &cfg, &field, budget).unwrap();
            include_mixed_solver_blockers(&mut facts);
            let cfg = facts.cfg();
            let mut queries = vec![BTreeSet::new(), cfg.nodes().iter().copied().collect()];
            for node in cfg.nodes() {
                queries.push(BTreeSet::from([*node]));
            }
            queries.push(BTreeSet::from([NodeId::new(usize::MAX)]));
            queries.push(BTreeSet::from([cfg.entry(), cfg.exit()]));
            for sites in queries {
                assert_eq!(
                    facts.reachability_blockers(&sites),
                    reference_reachability_blockers(&facts, &sites),
                    "{source}, budget {budget:?}, sites {sites:?}",
                );
            }
        }
    }
}
