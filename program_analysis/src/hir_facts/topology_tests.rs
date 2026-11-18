use std::collections::BTreeSet;
use std::fs;

use abstract_interpretation::graph::{EdgeId, FlowGraph, NodeId};
use abstract_interpretation::solver::{Blocker, SolveResult};
use parser::hir::{lift_project, HirProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::{CfgNodeKind, DefinitionCfg};
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
    let mut result = reference_deferred_control_blockers(facts, sites);
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

fn reference_deferred_control_blockers(
    facts: &AnalysisFacts<'_>,
    sites: &BTreeSet<NodeId>,
) -> BTreeSet<FactBlocker> {
    let cfg = facts.cfg();
    let mut blockers = BTreeSet::new();
    for site in sites {
        if facts.certified_dead_node(*site) {
            continue;
        }
        if let Some(node) = cfg.node(*site) {
            for control in &node.deferred_controls {
                if !facts.certified_dead_node(*control)
                    && !facts.specialized_guard(*control, &mut BTreeSet::new())
                {
                    blockers.insert(FactBlocker::DeferredControl(*control));
                }
            }
        }
        for branch in cfg.nodes() {
            let Some(CfgNodeKind::Branch {
                guard: parser::hir::ControlGuard::DeferredScalar, ..
            }) = cfg.node(*branch).map(|node| &node.kind)
            else {
                continue;
            };
            if facts.certified_dead_node(*branch) {
                continue;
            }
            if reference_reaches(cfg, *branch, &BTreeSet::from([*site]), None, &BTreeSet::new())
                && reference_reaches(
                    cfg,
                    *branch,
                    &BTreeSet::from([cfg.exit()]),
                    Some(*site),
                    &BTreeSet::new(),
                )
                && !facts.specialized_guard(*branch, &mut BTreeSet::new())
            {
                blockers.insert(FactBlocker::DeferredControl(*branch));
            }
        }
    }
    blockers
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
                    facts.reachability_blockers(&sites, &mut BTreeSet::new()),
                    reference_reachability_blockers(&facts, &sites),
                    "{source}, budget {budget:?}, sites {sites:?}",
                );
            }
        }
    }
}

#[test]
fn deferred_branch_cache_respects_aggregate_capacity_and_exact_fallback() {
    let hir = fixture("function Check(n){if(n){return 1;}if(n){return 2;}return 3;}");
    let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("Check").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let mut saw_mixed_cache = false;
    let mut saw_full_cache = false;
    for capacity in 0..=cfg.nodes().len() * 2 {
        let branches = facts.collect_deferred_branches(capacity);
        let mut retained = 0;
        let mut cached = 0;
        for branch in &branches {
            if let Some(nodes) = &branch.cached_reachable {
                retained += nodes.len();
                cached += 1;
            }
            for target in cfg.nodes() {
                assert_eq!(
                    branch.reaches(&cfg, *target),
                    reference_reaches(
                        &cfg,
                        branch.node,
                        &BTreeSet::from([*target]),
                        None,
                        &BTreeSet::new(),
                    ),
                );
            }
        }
        assert!(retained <= capacity);
        if capacity == 0 {
            assert_eq!(cached, 0);
        }
        saw_mixed_cache |= cached > 0 && cached < branches.len();
        saw_full_cache |= cached > 0 && cached == branches.len();
    }
    assert!(saw_mixed_cache);
    assert!(saw_full_cache);
}

#[test]
fn returned_array_elements_already_have_their_lexical_deferred_blocker() {
    let hir = fixture("function Check(n){if(n){return [1,2,3];}return [4];}");
    let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("Check").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let (site, control) = cfg
        .nodes()
        .iter()
        .find_map(|id| {
            let node = cfg.node(*id)?;
            let control = node.deferred_controls.first()?;
            facts.site_state(*id)?.variables()?;
            if facts.specialized_guard(*control, &mut BTreeSet::new())
                || facts.certified_dead_node(*control)
            {
                return None;
            }
            Some((*id, *control))
        })
        .unwrap();
    let sites = BTreeSet::from([site]);
    let expected = reference_deferred_control_blockers(&facts, &sites);
    assert!(expected.contains(&FactBlocker::DeferredControl(control)));
    assert_eq!(facts.deferred_control_blockers(&sites, &mut BTreeSet::new()), expected);
}

#[test]
fn deferred_blockers_match_old_walks_with_full_partial_and_disabled_caches() {
    let mut saw_multiple_controls = false;
    for source in [
        "function Check(n){if(n){return [1,2,3];}else if(n){return [4,5];}return [6];}",
        "function Check(n){while(n){if(n){return 1;}n--;}return 2;}",
        "template Check(n){if(n){var a=1;}if(n){var b=2;}var c=3;}",
        "template Check(){if(0){var hidden=Missing();}var live=3;}",
    ] {
        let hir = fixture(source);
        let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("Check").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        for budget in [Some(0), Some(1), Some(8), None] {
            for capacity in [0, 1, cfg.nodes().len(), 262_144] {
                let facts = analyze(&hir, &cfg, &field, budget).unwrap();
                let branches = facts.collect_deferred_branches(capacity);
                assert!(facts.deferred_branches.set(branches).is_ok());
                let cfg = facts.cfg();
                let mut queries = vec![BTreeSet::new(), cfg.nodes().iter().copied().collect()];
                for node in cfg.nodes() {
                    queries.push(BTreeSet::from([*node]));
                }
                queries.push(BTreeSet::from([NodeId::new(usize::MAX)]));
                for sites in queries {
                    let expected = reference_deferred_control_blockers(&facts, &sites);
                    let mut control_count = 0;
                    for blocker in &expected {
                        if let FactBlocker::DeferredControl(_) = blocker {
                            control_count += 1;
                        }
                    }
                    saw_multiple_controls |= control_count > 1;
                    assert_eq!(
                        facts.deferred_control_blockers(&sites, &mut BTreeSet::new()),
                        expected,
                        "{source}, {budget:?}, capacity {capacity}, sites {sites:?}",
                    );
                }
            }
        }
    }
    assert!(saw_multiple_controls);
}
