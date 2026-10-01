use abstract_interpretation::graph::FlowGraph;
use circomspect_program_analysis::hir_cfg::{build_cfg, BuildError, CfgNodeKind, EdgeKind};
use parser::hir::{lift_project, ControlGuard, DefinitionRef};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use std::fs;

fn fixture(source: &str) -> (parser::hir::LiftedProject, DefinitionRef) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-phase4-cfg-{}-{:?}",
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
    (lifted, definition)
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
    assert_eq!(return_edge.target, cfg.exit());
}

#[test]
fn symbolic_target_index_is_evaluated_before_witness_and_constraint() {
    let (project, definition) =
        fixture("template Check() { signal input i; signal output a[2]; a[i] <== 1; }");
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let mut positions: Vec<_> = cfg
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
    let assignment_index =
        positions.iter().find(|entry| entry.0 == "witness").unwrap().2.effect_index;
    positions.retain(|entry| entry.2.effect_index == assignment_index);
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
fn deferred_variable_write_remains_targeted_and_cannot_generate_a_constraint() {
    let (project, definition) = fixture("function Check(n){var x=n;if(x){return 1;}return 0;}");
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let kinds: Vec<_> = cfg.nodes().iter().map(|id| &cfg.node(*id).unwrap().kind).collect();
    assert!(kinds.iter().any(|kind| matches!(
        kind,
        CfgNodeKind::DeferredAssignment { target, .. }
            if project.hir.symbol(target.root).unwrap().name == "x"
    )));
    assert!(kinds.iter().any(|kind| matches!(
        kind,
        CfgNodeKind::Branch { guard: ControlGuard::DeferredScalar, .. }
    )));
    assert!(kinds.iter().all(|kind| !matches!(kind, CfgNodeKind::Constraint { .. })));
}

#[test]
fn declaration_dimensions_are_evaluated_before_declaration() {
    let (project, definition) = fixture("template Check(){var n=2; signal output a[n];}");
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let declarations: Vec<_> = cfg
        .nodes()
        .iter()
        .filter_map(|id| {
            let node = cfg.node(*id).unwrap();
            let CfgNodeKind::Declaration { .. } = node.kind else { return None };
            Some((*id, node.origin.unwrap()))
        })
        .collect();
    let a = declarations
        .iter()
        .find(|(_, origin)| {
            let block = project.hir.block(origin.block).unwrap();
            let parser::hir::Effect::Declaration { symbol, .. } =
                &block.effects[origin.effect_index]
            else {
                return false;
            };
            project.hir.symbol(*symbol).unwrap().name == "a"
        })
        .unwrap();
    let dimension = cfg
        .nodes()
        .iter()
        .filter_map(|id| {
            let node = cfg.node(*id).unwrap();
            let CfgNodeKind::Evaluate(expression) = node.kind else { return None };
            (node.origin.unwrap().effect_index == a.1.effect_index).then_some((*id, expression))
        })
        .next()
        .unwrap();
    assert!(dimension.0 < a.0);
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
    let branches: Vec<_> = cfg
        .nodes()
        .iter()
        .filter_map(|id| {
            let node = cfg.node(*id)?;
            let CfgNodeKind::Branch { condition, guard } = &node.kind else { return None };
            Some((*id, *condition, *guard, node.origin?))
        })
        .collect();
    assert_eq!(branches.len(), 1);
    assert_eq!(branches[0].2, ControlGuard::CheckedCompileTime);
    assert_eq!(branches[0].3.expression, Some(branches[0].1));
    let outgoing: Vec<_> = cfg
        .edges()
        .iter()
        .filter_map(|id| cfg.edge(*id))
        .filter(|edge| edge.source == branches[0].0)
        .collect();
    assert_eq!(outgoing.len(), 2);
    assert!(outgoing.iter().all(|edge| {
        edge.payload.condition == Some(branches[0].1)
            && edge.payload.guard == Some(ControlGuard::CheckedCompileTime)
    }));
}

#[test]
fn deferred_parameter_guard_is_preserved_on_branch_and_edges() {
    let (project, definition) =
        fixture("template Check(n){signal output y; if(n){y <== 1;}else{y <== 2;}}");
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let branch = cfg
        .nodes()
        .iter()
        .find_map(|id| {
            let CfgNodeKind::Branch { guard: ControlGuard::DeferredScalar, .. } =
                &cfg.node(*id)?.kind
            else {
                return None;
            };
            Some(*id)
        })
        .unwrap();
    let outgoing: Vec<_> = cfg
        .edges()
        .iter()
        .filter_map(|id| cfg.edge(*id))
        .filter(|edge| edge.source == branch)
        .collect();
    assert_eq!(outgoing.len(), 2);
    assert!(outgoing
        .iter()
        .all(|edge| { edge.payload.guard == Some(ControlGuard::DeferredScalar) }));
}

#[test]
fn effects_after_return_do_not_enter_the_cfg() {
    let (project, definition) = fixture("function Check(){var x=1; return x; var y=0; y++;}");
    let cfg = build_cfg(&project.hir, definition).unwrap();
    assert!(!cfg.nodes().iter().any(|id| {
        let Some(node) = cfg.node(*id) else { return false };
        matches!(&node.kind, CfgNodeKind::Opaque(_))
    }));
    let return_edges: Vec<_> = cfg
        .edges()
        .iter()
        .filter_map(|id| cfg.edge(*id))
        .filter(|edge| edge.payload.kind == EdgeKind::Return)
        .collect();
    assert_eq!(return_edges.len(), 1);
    assert_eq!(return_edges[0].target, cfg.exit());
}
