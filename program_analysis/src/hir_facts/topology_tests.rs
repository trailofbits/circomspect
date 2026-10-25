use std::collections::BTreeSet;
use std::fs;

use abstract_interpretation::graph::{EdgeId, FlowGraph, NodeId};
use parser::hir::{lift_project, HirProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::DefinitionCfg;
use crate::hir_facts::{analyze, AnalysisFacts, FieldContext};

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
