// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use std::fs;

use abstract_interpretation::graph::{EdgeId, FlowGraph};
use circomspect_program_analysis::hir_cfg::{build_cfg, CfgNodeKind, EdgeKind};
use circomspect_program_analysis::hir_facts::{analyze, FactBlocker, FieldContext};
use circomspect_program_analysis::interprocedural::{CallOwner, CallReachability, ProjectSummaries};
use parser::hir::{lift_project, ControlGuard};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> (parser::hir::LiftedProject, parser::hir::DefinitionRef) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-edge-facts-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    let definition = lifted.hir.definition("Check").unwrap();
    (lifted, definition)
}

#[test]
fn pruned_branch_edges_stay_distinct_when_both_rejoin_a_reachable_node() {
    let (lifted, definition) = fixture("template Check(){if(0){} signal output y;y<==1;}");
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&lifted.hir, &cfg, &field, None).unwrap();
    let branch = cfg
        .nodes()
        .iter()
        .find_map(|id| {
            let CfgNodeKind::Branch { .. } = &cfg.node(*id)?.kind else { return None };
            Some(*id)
        })
        .unwrap();
    let mut edges = Vec::new();
    for id in cfg.edges() {
        let edge = cfg.edge(*id).unwrap();
        if edge.source == branch {
            edges.push((edge.payload.kind, edge.target, facts.reachable_edge(*id)));
        }
    }
    assert_eq!(edges.len(), 2);
    assert_eq!(edges[0].1, edges[1].1);
    for (kind, _, reachability) in edges {
        assert_eq!(
            reachability.certified(),
            Some(&match kind {
                EdgeKind::True => false,
                EdgeKind::False => true,
                EdgeKind::Normal | EdgeKind::Loop | EdgeKind::Return => panic!("branch edge"),
            })
        );
    }
    assert_eq!(
        facts.reachable_edge(EdgeId::new(10_000)).unavailable(),
        Some(&std::collections::BTreeSet::from([FactBlocker::ForeignQuery]))
    );
}

#[test]
fn concrete_main_argument_selects_the_matching_branch_edge() {
    for (argument, expected) in [(0, EdgeKind::False), (1, EdgeKind::True)] {
        let source = format!(
            "template Check(n){{if(n){{}}signal output y;y<==1;}} component main=Check({argument});"
        );
        let (lifted, definition) = fixture(&source);
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let main = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph().reachable_main_call(main.id(), provider.hir())
        else {
            panic!("checked main call")
        };
        let evidence = provider.main_evidence(&call).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let branch = cfg
            .nodes()
            .iter()
            .find_map(|id| {
                let CfgNodeKind::Branch { .. } = &cfg.node(*id)?.kind else { return None };
                Some(*id)
            })
            .unwrap();
        for id in cfg.edges() {
            let edge = cfg.edge(*id).unwrap();
            if edge.source == branch {
                assert_eq!(
                    facts.reachable_edge(*id).certified(),
                    Some(&(edge.payload.kind == expected))
                );
            }
        }
    }
}

#[test]
fn loop_back_edge_reachability_uses_the_same_fixed_point_as_nodes() {
    let (lifted, definition) = fixture("function Check(){for(var i=0;1;i=i){} return 0;}");
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&lifted.hir, &cfg, &field, None).unwrap();
    let loop_edges: Vec<_> = cfg
        .edges()
        .iter()
        .filter(|id| cfg.edge(**id).unwrap().payload.kind == EdgeKind::Loop)
        .copied()
        .collect();
    assert!(
        !loop_edges.is_empty(),
        "{:?}",
        cfg.edges().iter().map(|id| cfg.edge(*id).unwrap().payload.kind).collect::<Vec<_>>()
    );
    assert!(
        loop_edges.iter().any(|id| facts.reachable_edge(*id).certified() == Some(&true)),
        "{:?}",
        loop_edges.iter().map(|id| facts.reachable_edge(*id)).collect::<Vec<_>>()
    );
}

#[test]
fn incomplete_solver_and_opaque_source_never_certify_an_edge() {
    let (lifted, definition) = fixture("template Check(){var x=Missing();}");
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let budget = analyze(&lifted.hir, &cfg, &field, Some(0)).unwrap();
    let blocked = cfg
        .edges()
        .iter()
        .find(|id| budget.reachable_edge(**id).unavailable().is_some())
        .copied()
        .unwrap();
    assert!(budget
        .reachable_edge(blocked)
        .unavailable()
        .unwrap()
        .iter()
        .find_map(|reason| {
            let FactBlocker::Budget(node) = reason else { return None };
            Some(*node)
        })
        .is_some());
    let opaque = analyze(&lifted.hir, &cfg, &field, None).unwrap();
    let blocked = cfg
        .edges()
        .iter()
        .find(|id| opaque.reachable_edge(**id).unavailable().is_some())
        .copied()
        .unwrap();
    assert!(opaque
        .reachable_edge(blocked)
        .unavailable()
        .unwrap()
        .iter()
        .find_map(|reason| {
            if let FactBlocker::OpaqueNode(_, _) = reason {
                return Some(());
            }
            if let FactBlocker::OpaqueEdge(_, _) = reason {
                return Some(());
            }
            None
        })
        .is_some());
}

#[test]
fn dead_nested_symbolic_control_has_certified_dead_edges_but_live_control_blocks() {
    for (source, dead) in [
        ("template Check(n){var x=0;if(0){if(n){x=1;}}}", true),
        ("template Check(n){var x=0;if(n){x=1;}}", false),
    ] {
        let (lifted, definition) = fixture(source);
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let facts = analyze(&lifted.hir, &cfg, &field, None).unwrap();
        let branch = cfg
            .nodes()
            .iter()
            .find(|id| {
                let Some(node) = cfg.node(**id) else { return false };
                let CfgNodeKind::Branch { guard: ControlGuard::DeferredScalar, .. } = node.kind
                else {
                    return false;
                };
                true
            })
            .copied()
            .unwrap();
        let edges: Vec<_> = cfg
            .edges()
            .iter()
            .filter(|id| cfg.edge(**id).is_some_and(|edge| edge.source == branch))
            .copied()
            .collect();
        assert_eq!(edges.len(), 2);
        let mut blocked = 0;
        for edge in &edges {
            let reachability = facts.reachable_edge(*edge);
            if dead {
                assert_eq!(reachability.certified(), Some(&false));
            } else if reachability.unavailable().is_some_and(|blockers| {
                blockers.iter().any(|blocker| {
                    let FactBlocker::DeferredControl(_) = blocker else { return false };
                    true
                })
            }) {
                blocked += 1;
            }
        }
        if dead {
            let budget = analyze(&lifted.hir, &cfg, &field, Some(0)).unwrap();
            assert!(edges.iter().all(|edge| budget.reachable_edge(*edge).certified().is_none()));
        } else {
            assert!(blocked > 0, "live symbolic control must retain a blocker");
        }
    }
}
