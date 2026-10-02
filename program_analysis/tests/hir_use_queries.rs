use std::fs;

use abstract_interpretation::graph::FlowGraph;
use circomspect_program_analysis::hir_cfg::{build_cfg, CfgNodeKind};
use circomspect_program_analysis::hir_facts::{analyze, FactBlocker, FieldContext};
use parser::hir::{lift_project, AccessPath, DefinitionRef, HirProject, SymbolId};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> (HirProject, DefinitionRef) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-use-queries-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    let definition = lifted.hir.definition("Check").unwrap();
    (lifted.hir, definition)
}

fn parameter(hir: &HirProject, definition: DefinitionRef) -> SymbolId {
    let DefinitionRef::Function(id) = definition else { panic!("expected function") };
    hir.function(id).unwrap().parameters[0]
}

fn assignment(
    cfg: &circomspect_program_analysis::hir_cfg::DefinitionCfg,
) -> (abstract_interpretation::graph::NodeId, AccessPath) {
    for id in cfg.nodes() {
        let Some(node) = cfg.node(*id) else { continue };
        if let CfgNodeKind::Assignment { target, .. } = &node.kind {
            return (*id, target.clone());
        }
    }
    panic!("expected assignment")
}

#[test]
fn assigned_value_is_dead_after_node_but_live_when_returned() {
    for (source, expected) in [
        ("function Check(){var x=1;return 7;}", false),
        ("function Check(){var x=1;return x;}", true),
    ] {
        let (hir, definition) = fixture(source);
        let cfg = build_cfg(&hir, definition).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let facts = analyze(&hir, &cfg, &field, None).unwrap();
        let (node, path) = assignment(&cfg);
        assert_eq!(facts.live_after(node, &path).certified(), Some(&expected));
    }
}

#[test]
fn exact_array_element_liveness_respects_distinct_and_symbolic_indices() {
    for (source, expected) in [
        ("function Check(){var x[2];x[0]=1;return x[1];}", Some(false)),
        ("function Check(){var x[2];x[0]=1;return x[0];}", Some(true)),
        ("function Check(i){var x[2];x[0]=1;return x[i];}", None),
    ] {
        let (hir, definition) = fixture(source);
        let cfg = build_cfg(&hir, definition).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let facts = analyze(&hir, &cfg, &field, None).unwrap();
        let (node, path) = assignment(&cfg);
        let result = facts.live_after(node, &path);
        assert_eq!(result.certified().copied(), expected, "{source}: {result:?}");
    }
}

#[test]
fn parameter_query_counts_reachable_reads_after_unrelated_overwrites() {
    for (source, expected) in [
        ("function Check(p){return 7;}", false),
        ("function Check(p){var x=0;x=1;return p;}", true),
        ("function Check(p){if(0){var x=p;}return 7;}", false),
        ("function Check(p){if(p){return 1;}return 7;}", true),
    ] {
        let (hir, definition) = fixture(source);
        let cfg = build_cfg(&hir, definition).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let facts = analyze(&hir, &cfg, &field, None).unwrap();
        let result = facts.parameter_read(parameter(&hir, definition));
        assert_eq!(result.certified(), Some(&expected), "{source}: {result:?}");
    }
}

#[test]
fn deferred_parameter_overwrite_cannot_certify_no_later_read() {
    let (hir, definition) = fixture("function Check(p){p=1;return p;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let result = facts.parameter_read(parameter(&hir, definition));
    assert_ne!(result.certified(), Some(&false));
}

#[test]
fn symbolic_parameter_index_read_cannot_certify_no_read() {
    let (hir, definition) = fixture("function Check(p){return p[0];}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let result = facts.parameter_read(parameter(&hir, definition));
    assert_ne!(result.certified(), Some(&false));
}

#[test]
fn symbolic_assertion_of_parameter_cannot_certify_no_read() {
    let (hir, definition) = fixture("function Check(p){assert(p);return 7;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let result = facts.parameter_read(parameter(&hir, definition));
    assert_ne!(result.certified(), Some(&false));
}

#[test]
fn every_small_budget_keeps_a_reachable_parameter_read_from_becoming_unused() {
    let source = "function Check(p){var x=0;for(var i=0;i<17;i++){x+=p;}return x;}";
    let (hir, definition) = fixture(source);
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    for budget in 0..160 {
        let facts = analyze(&hir, &cfg, &field, Some(budget)).unwrap();
        let result = facts.parameter_read(parameter(&hir, definition));
        assert_ne!(result.certified(), Some(&false), "budget {budget}: {result:?}");
    }
}

#[test]
fn parameter_read_rejects_a_symbol_from_another_definition() {
    let source = "function Check(p){return 7;} function Other(q){return q;}";
    let (hir, definition) = fixture(source);
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let other = hir.definition("Other").unwrap();
    let result = facts.parameter_read(parameter(&hir, other));
    assert!(result.unavailable().unwrap().contains(&FactBlocker::ForeignDefinition));
}

#[test]
fn opaque_dependency_blocks_negative_parameter_proof_but_unrelated_work_does_not() {
    for (source, expected) in [
        ("function Check(p){var x=p;x=1;return x;}", None),
        ("function Check(p){var x=0;x/=0;return 7;}", Some(false)),
    ] {
        let (hir, definition) = fixture(source);
        let cfg = build_cfg(&hir, definition).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let facts = analyze(&hir, &cfg, &field, None).unwrap();
        let result = facts.parameter_read(parameter(&hir, definition));
        assert_eq!(result.certified().copied(), expected, "{source}: {result:?}");
    }
}

#[test]
fn incomplete_backward_solver_never_certifies_no_read() {
    let (hir, definition) = fixture("function Check(p){return 7;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, Some(0)).unwrap();
    let result = facts.parameter_read(parameter(&hir, definition));
    let blockers = result.unavailable().unwrap();
    assert!(blockers.iter().any(|blocker| match blocker {
        FactBlocker::Budget(_) => true,
        FactBlocker::OpaqueNode(_, _)
        | FactBlocker::OpaqueEdge(_, _)
        | FactBlocker::ExternalSummary
        | FactBlocker::AggregateAccess
        | FactBlocker::DeferredShape(_)
        | FactBlocker::AggregateConstraint(_)
        | FactBlocker::DeferredControl(_)
        | FactBlocker::OpaqueExpression(_)
        | FactBlocker::UnsupportedRelation(_)
        | FactBlocker::WitnessWrite(_, _)
        | FactBlocker::SignalRead(_, _)
        | FactBlocker::MissingExit
        | FactBlocker::ForeignQuery
        | FactBlocker::ForeignDefinition => false,
    }));
}
