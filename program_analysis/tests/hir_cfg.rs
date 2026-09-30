use abstract_interpretation::graph::FlowGraph;
use circomspect_program_analysis::hir_cfg::{build_cfg, BuildError, CfgNodeKind, EdgeKind};
use parser::hir::{lower_project, DefinitionRef};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use std::fs;

fn fixture(source: &str) -> (parser::hir::LoweredProject, DefinitionRef) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-phase4-cfg-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lowered = lower_project(&loaded);
    assert!(lowered.syntax_diagnostics.is_empty(), "{:?}", lowered.syntax_diagnostics);
    assert!(lowered.diagnostics.is_empty(), "{:?}", lowered.diagnostics);
    let definition = lowered.hir.definition("Check").unwrap();
    (lowered, definition)
}

#[test]
fn witness_constraint_and_assert_are_distinct() {
    let (project, definition) = fixture(
        "template Check() { signal input x; signal output a; signal output b; \
         a <-- x; b <== x; a === 7; assert(b == 7); }",
    );
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let kinds: Vec<_> = cfg.nodes().iter().map(|id| &cfg.node(*id).unwrap().kind).collect();
    assert_eq!(kinds.iter().filter(|kind| matches!(kind, CfgNodeKind::Witness { .. })).count(), 2);
    assert_eq!(
        kinds.iter().filter(|kind| matches!(kind, CfgNodeKind::Constraint { .. })).count(),
        2
    );
    assert_eq!(kinds.iter().filter(|kind| matches!(kind, CfgNodeKind::Assert { .. })).count(), 1);
    let witness_only =
        kinds.iter().position(|kind| matches!(kind, CfgNodeKind::Witness { .. })).unwrap();
    let constrained =
        kinds.iter().position(|kind| matches!(kind, CfgNodeKind::Constraint { .. })).unwrap();
    assert!(witness_only < constrained);
    let witness = cfg.node(cfg.nodes()[witness_only]).unwrap().origin.unwrap();
    let constraint = cfg.node(cfg.nodes()[constrained]).unwrap().origin.unwrap();
    assert!(witness.expression.is_some());
    assert!(constraint.expression.is_some());
    assert!(witness.span.start() < constraint.span.end());
}

#[test]
fn loop_back_edge_and_return_preserve_exit() {
    let (project, definition) =
        fixture("function Check() { var i = 0; while (i < 2) { i++; } return i; }");
    let cfg = build_cfg(&project.hir, definition).unwrap();
    assert!(cfg.edges().iter().any(|id| cfg.edge(*id).unwrap().payload.kind == EdgeKind::Loop));
    let return_edge = cfg
        .edges()
        .iter()
        .map(|id| cfg.edge(*id).unwrap())
        .find(|edge| edge.payload.kind == EdgeKind::Return)
        .unwrap();
    assert_eq!(return_edge.target, cfg.exit);
}

#[test]
fn symbolic_target_index_is_evaluated_before_witness_and_constraint() {
    let (project, definition) =
        fixture("template Check() { signal input i; signal output a[2]; a[i] <== 1; }");
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let positions: Vec<_> = cfg
        .nodes()
        .iter()
        .filter_map(|id| {
            let node = cfg.node(*id).unwrap();
            match &node.kind {
                CfgNodeKind::Evaluate(expr) => Some(("eval", Some(*expr), node.origin.unwrap())),
                CfgNodeKind::Witness { .. } => Some(("witness", None, node.origin.unwrap())),
                CfgNodeKind::Constraint { .. } => Some(("constraint", None, node.origin.unwrap())),
                _ => None,
            }
        })
        .collect();
    assert_eq!(
        positions.iter().map(|entry| entry.0).collect::<Vec<_>>(),
        ["eval", "eval", "witness", "constraint"]
    );
    assert_eq!(positions[0].2.effect_index, positions[2].2.effect_index);
    assert_eq!(positions[2].2.effect_index, positions[3].2.effect_index);
    assert_eq!(positions[2].2.expression, positions[3].2.expression);
    assert!(positions[0].2.expression.is_some());
}

#[test]
fn foreign_definition_returns_a_typed_error() {
    let (first, definition) = fixture("template Check() {}");
    let (other, _) = fixture("template Check() { signal x; }");
    assert!(matches!(build_cfg(&other.hir, definition), Err(BuildError::ForeignDefinition)));
    assert!(build_cfg(&first.hir, definition).is_ok());
}

#[test]
fn conditional_has_distinct_true_false_paths() {
    let (project, definition) = fixture(
        "template Check() { signal input x; signal output y; \
         if (1) { y <== x; } else { y <-- x; } }",
    );
    let cfg = build_cfg(&project.hir, definition).unwrap();
    assert_eq!(cfg.entries().len(), 1);
    assert_eq!(cfg.exits().len(), 1);
    assert!(cfg.edges().iter().any(|id| cfg.edge(*id).unwrap().payload.kind == EdgeKind::True));
    assert!(cfg.edges().iter().any(|id| cfg.edge(*id).unwrap().payload.kind == EdgeKind::False));
}
