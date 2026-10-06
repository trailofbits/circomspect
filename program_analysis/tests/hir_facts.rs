// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::assert_is_empty,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use abstract_interpretation::graph::FlowGraph;
use circomspect_program_analysis::hir_cfg::{build_cfg, CfgNodeKind};
use circomspect_program_analysis::hir_facts::{
    analyze, AnalysisError, FactBlocker, FieldContext, Incidence, Range,
};
use parser::hir::{
    lift_project, AccessPath, AccessStep, ArrayIndex, ControlGuard, DefinitionRef, Effect,
    ExprKind, HirProject, LiftedProject, SemanticCode,
};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use std::collections::BTreeSet;
use std::fs;
use program_structure::utils::constants::Curve;

fn lift_fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-phase4-facts-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

fn fixture(source: &str) -> (HirProject, DefinitionRef) {
    let lifted = lift_fixture(source);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    let definition = lifted.hir.definition("Check").unwrap();
    (lifted.hir, definition)
}

fn assigned_path(hir: &HirProject, definition: DefinitionRef, name: &str) -> AccessPath {
    let DefinitionRef::Template(id) = definition else { panic!("expected template") };
    let block = hir.block(hir.template(id).unwrap().body).unwrap();
    block
        .effects
        .iter()
        .filter_map(|effect| match effect {
            Effect::WitnessAssignment { target, .. }
            | Effect::ConstraintAssignment { target, .. } => Some(target),
            _ => None,
        })
        .find(|path| hir.symbol(path.root).unwrap().name == name)
        .unwrap()
        .clone()
}

fn last_assigned_path(hir: &HirProject, definition: DefinitionRef, name: &str) -> AccessPath {
    let DefinitionRef::Template(id) = definition else { panic!("expected template") };
    let block = hir.block(hir.template(id).unwrap().body).unwrap();
    block
        .effects
        .iter()
        .filter_map(|effect| match effect {
            Effect::WitnessAssignment { target, .. }
            | Effect::ConstraintAssignment { target, .. }
                if hir.symbol(target.root).unwrap().name == name =>
            {
                Some(target.clone())
            }
            _ => None,
        })
        .next_back()
        .unwrap()
}

fn expression_path(hir: &HirProject, name: &str, minimum_steps: usize) -> AccessPath {
    hir.expressions()
        .iter()
        .find_map(|expression| match &expression.kind {
            ExprKind::Access(path)
                if hir.symbol(path.root).is_some_and(|symbol| symbol.name == name)
                    && path.steps.len() >= minimum_steps =>
            {
                Some(path.clone())
            }
            _ => None,
        })
        .unwrap()
}

#[test]
fn witness_value_and_assert_do_not_prove_constraint_incidence() {
    let (hir, definition) =
        fixture("template Check() { signal output y; y <-- 7; assert(y == 7); }");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = assigned_path(&hir, definition, "y");
    assert_eq!(facts.incidence(&path).certified(), Some(&Incidence::Zero));
    assert_eq!(facts.constraint_fixed(&path).certified(), Some(&None));
}

#[test]
fn deferred_variable_shape_blocks_exact_range_after_scalar_overwrite() {
    let (hir, definition) = fixture("function Check(n){var x=n;x=0;return x;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let returned = cfg
        .nodes()
        .iter()
        .find_map(|id| match cfg.node(*id).map(|node| &node.kind) {
            Some(CfgNodeKind::Return(value)) => Some(*value),
            _ => None,
        })
        .unwrap();
    assert!(facts.range(returned).certified().is_none());
    assert!(facts
        .range(returned)
        .unavailable()
        .unwrap()
        .contains(&FactBlocker::DeferredShape(returned)));
}

#[test]
fn statically_pruned_call_has_no_reachable_evaluation_site() {
    let (hir, definition) = fixture(
        "template Child(){signal output out;out<==1;} \
         template Check(){if(0){component c=Child();}signal output y;y<==1;}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let call = hir
        .expressions()
        .iter()
        .find_map(|expression| match &expression.kind {
            ExprKind::Call { target: parser::hir::CallTarget::Template(_), .. } => {
                Some(expression.id)
            }
            _ => None,
        })
        .unwrap();
    assert_eq!(facts.reachable_expression(call).certified(), Some(&false));
}

#[test]
fn component_call_is_reachable_before_its_opaque_effect() {
    let (hir, definition) = fixture("template Child(){} template Check(){component c=Child();}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let call = hir
        .expressions()
        .iter()
        .find_map(|expression| match &expression.kind {
            ExprKind::Call { target: parser::hir::CallTarget::Template(_), .. } => {
                Some(expression.id)
            }
            _ => None,
        })
        .unwrap();
    assert_eq!(facts.reachable_expression(call).certified(), Some(&true));
}

#[test]
fn deferred_control_cannot_certify_call_reachability() {
    let (hir, definition) =
        fixture("template Child(){} template Check(n){if(n){component c=Child();}}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let call = hir
        .expressions()
        .iter()
        .find_map(|expression| match &expression.kind {
            ExprKind::Call { target: parser::hir::CallTarget::Template(_), .. } => {
                Some(expression.id)
            }
            _ => None,
        })
        .unwrap();
    assert!(facts.reachable_expression(call).certified().is_none());
}

#[test]
fn late_equality_revokes_zero_incidence() {
    let (hir, definition) = fixture("template Check() { signal output y; y <-- 7; y === 7; }");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = assigned_path(&hir, definition, "y");
    assert_eq!(facts.incidence(&path).certified(), Some(&Incidence::Must));
}

#[test]
fn constraint_assignment_generates_incidence_and_fixed_value() {
    let (hir, definition) = fixture("template Check() { signal output y; y <== 7; }");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = assigned_path(&hir, definition, "y");
    assert_eq!(facts.incidence(&path).certified(), Some(&Incidence::Must));
    assert_eq!(facts.constraint_fixed(&path).certified(), Some(&Some(field.canonical(7.into()))));
}

#[test]
fn exhausted_budget_never_certifies_a_provisional_zero() {
    let (hir, definition) = fixture("template Check() { signal output y; y <== 7; }");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, Some(1)).unwrap();
    let path = assigned_path(&hir, definition, "y");
    assert!(facts.incidence(&path).unavailable().is_some());
}

#[test]
fn pending_alternative_branch_never_certifies_provisional_must() {
    let (hir, definition) =
        fixture("template Check(){signal output x; if(0 << 513){x <== 1;}else{x <-- 1;}}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let DefinitionRef::Template(id) = definition else { panic!("template fixture") };
    let body = hir.block(hir.template(id).unwrap().body).unwrap();
    let Some(Effect::If { then_block, .. }) =
        body.effects.iter().find(|effect| matches!(effect, Effect::If { .. }))
    else {
        panic!("if effect")
    };
    let x = hir
        .block(*then_block)
        .unwrap()
        .effects
        .iter()
        .find_map(|effect| {
            let Effect::ConstraintAssignment { target, .. } = effect else { return None };
            Some(target.clone())
        })
        .unwrap();
    for budget in 0..=cfg.nodes().len() * 4 {
        let facts = analyze(&hir, &cfg, &field, Some(budget)).unwrap();
        assert_ne!(facts.incidence(&x).certified(), Some(&Incidence::Must), "budget {budget}");
    }
}

#[test]
fn branch_must_constraint_needs_proven_compile_time_choice() {
    let (hir, definition) = fixture(
        "template Check(n) { signal output y; if (n) { y <== 7; } else { y <-- 7; } y <-- 1; }",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = last_assigned_path(&hir, definition, "y");
    assert!(facts.incidence(&path).unavailable().is_some());
    let DefinitionRef::Template(id) = definition else { panic!("template fixture") };
    let body = hir.block(hir.template(id).unwrap().body).unwrap();
    assert!(body.effects.iter().any(|effect| {
        matches!(effect, Effect::If { guard: ControlGuard::DeferredScalar, .. })
    }));

    let (hir, definition) = fixture(
        "template Check() { signal output y; if (1) { y <== 7; } else { y <-- 7; } y <-- 1; }",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = last_assigned_path(&hir, definition, "y");
    assert_eq!(facts.incidence(&path).certified(), Some(&Incidence::Must));
}

#[test]
fn different_sites_on_every_arm_prove_incidence_independent_of_fixed_value() {
    let field = FieldContext::for_curve(Curve::Bn254);
    for (otherwise, fixed) in [("1", Some(field.canonical(1.into()))), ("2", None)] {
        let source = format!(
            "template Check(){{signal input x; if(0 << 513){{x===1;}}else{{x==={otherwise};}}}}"
        );
        let (hir, definition) = fixture(&source);
        let cfg = build_cfg(&hir, definition).unwrap();
        let facts = analyze(&hir, &cfg, &field, None).unwrap();
        let x = expression_path(&hir, "x", 0);
        assert_eq!(facts.incidence(&x).certified(), Some(&Incidence::Must));
        assert_eq!(facts.constraint_fixed(&x).certified(), Some(&fixed));
    }
}

#[test]
fn arithmetic_access_on_each_branch_proves_must_incidence() {
    let (hir, definition) =
        fixture("template Check(){signal input x; if(0 << 513){x+1===0;}else{x+2===0;}}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    assert_eq!(facts.incidence(&x).certified(), Some(&Incidence::Must));
}

#[test]
fn known_ternary_discards_dependencies_of_its_unselected_arm() {
    let (hir, definition) =
        fixture("template Check(){signal input x; signal output y; y<==(0 ? x : 1);}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    assert_eq!(facts.incidence(&x).certified(), Some(&Incidence::Zero));
}

#[test]
fn algebraically_cancelled_access_has_zero_generated_constraint_incidence() {
    for source in [
        "template Check(){signal input x; signal output y; y<==0*x;}",
        "template Check(){signal input x; x===x;}",
        "template Check(){signal input x; x-x===0;}",
    ] {
        let (hir, definition) = fixture(source);
        let cfg = build_cfg(&hir, definition).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let facts = analyze(&hir, &cfg, &field, None).unwrap();
        let x = expression_path(&hir, "x", 0);
        assert_eq!(facts.incidence(&x).certified(), Some(&Incidence::Zero), "{source}");
    }
}

#[test]
fn liveness_ignores_a_branch_pruned_by_a_known_local_value() {
    let (hir, definition) =
        fixture("function Check(){var x=0; var t=0; if(t){return x;} return 1;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    let t = hir.symbols().iter().find(|symbol| symbol.name == "t").unwrap().id;
    let after_x_write = cfg
        .nodes()
        .iter()
        .find_map(|id| {
            let node = cfg.node(*id)?;
            let CfgNodeKind::Assignment { target, .. } = &node.kind else { return None };
            (target.root == t).then_some(*id)
        })
        .unwrap();
    assert_eq!(facts.live_before(after_x_write, &x).certified(), Some(&false));
}

#[test]
fn no_argument_function_call_does_not_touch_an_unrelated_signal() {
    let (hir, definition) = fixture(
        "function F(){return 1;} template Check(){signal input x;var t=x;signal output y;y<==F();}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    assert_eq!(facts.incidence(&x).certified(), Some(&Incidence::Zero));
}

#[test]
fn missing_call_inside_constraint_cannot_certify_zero_for_known_operand() {
    let lifted = lift_fixture("template Check(){signal input x;signal output y;y<==x+Missing();}");
    assert_eq!(lifted.diagnostics.len(), 1);
    assert_eq!(lifted.diagnostics[0].code, SemanticCode::MissingCall);
    let hir = lifted.hir;
    let definition = hir.definition("Check").unwrap();
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    assert!(facts.incidence(&x).unavailable().is_some());
}

#[test]
fn function_call_blocks_only_argument_dependent_incidence() {
    let (hir, definition) = fixture(
        "function F(a){return a;} template Check(){signal input x;signal output y,z;\
         y<==F(x);z<==1;}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    let y = hir
        .template(match definition {
            DefinitionRef::Template(id) => id,
            _ => panic!("template"),
        })
        .unwrap();
    let y = hir
        .block(y.body)
        .unwrap()
        .effects
        .iter()
        .find_map(|effect| {
            let Effect::OpaqueAssignment { target, .. } = effect else { return None };
            Some(target)
        })
        .unwrap();
    let z = assigned_path(&hir, definition, "z");
    assert!(facts
        .incidence(&x)
        .unavailable()
        .is_some_and(|blockers| { blockers.contains(&FactBlocker::ExternalSummary) }));
    assert!(facts.incidence(y).unavailable().is_some());
    assert_eq!(facts.incidence(&z).certified(), Some(&Incidence::Must));
    assert_eq!(
        cfg.nodes()
            .iter()
            .filter_map(|id| cfg.node(*id))
            .filter(|node| matches!(node.kind, CfgNodeKind::Constraint { .. }))
            .count(),
        1
    );
}

#[test]
fn opaque_variable_call_does_not_invent_unrelated_constraint_dependency() {
    let (hir, definition) = fixture(
        "function F(a){return a;} template Check(){signal input x,z;var u=z;var t=F(x);\
         signal output y,w;y<==t;w<==1;}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    let z = expression_path(&hir, "z", 0);
    let w = assigned_path(&hir, definition, "w");
    assert!(facts.incidence(&x).unavailable().is_some());
    assert_eq!(facts.incidence(&z).certified(), Some(&Incidence::Zero));
    assert_eq!(facts.incidence(&w).certified(), Some(&Incidence::Must));
}

#[test]
fn fresh_local_without_signal_dependencies_preserves_neighboring_constraint_facts() {
    let (hir, definition) =
        fixture("template Check(){signal input z;var u=z;var t;signal output y,w;y<==t;w<==1;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let z = expression_path(&hir, "z", 0);
    let w = assigned_path(&hir, definition, "w");
    assert_eq!(facts.incidence(&z).certified(), Some(&Incidence::Zero));
    assert_eq!(facts.incidence(&w).certified(), Some(&Incidence::Must));
    assert_eq!(facts.constraint_fixed(&w).certified(), Some(&Some(field.canonical(1.into()))));
}

#[test]
fn scalar_local_declaration_has_compiler_default_zero_without_a_constraint() {
    let (hir, definition) = fixture("function Check(){var t;return t;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let t = expression_path(&hir, "t", 0);
    let expression = hir
        .expressions()
        .iter()
        .find(|expression| matches!(&expression.kind, ExprKind::Access(path) if path == &t))
        .unwrap()
        .id;
    let declaration = cfg
        .nodes()
        .iter()
        .find(|id| matches!(cfg.node(**id).unwrap().kind, CfgNodeKind::Declaration { .. }))
        .copied()
        .unwrap();
    assert_eq!(facts.range(expression).certified(), Some(&Range::Exact(field.canonical(0.into()))));
    assert_eq!(facts.live_before(declaration, &t).certified(), Some(&false));
    assert!(cfg
        .nodes()
        .iter()
        .all(|id| !matches!(cfg.node(*id).unwrap().kind, CfgNodeKind::Constraint { .. })));
}

#[test]
fn default_zero_local_fixes_output_only_through_a_generated_assignment() {
    let (hir, definition) = fixture("template Check(){var t;signal output y;y<==t;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let y = assigned_path(&hir, definition, "y");
    assert_eq!(facts.constraint_fixed(&y).certified(), Some(&Some(field.canonical(0.into()))));
}

#[test]
fn anonymous_output_dependencies_leave_neighboring_constraint_certified() {
    let (hir, definition) = fixture(
        "template Child(){signal input in;signal output out;out<==in;} \
         template Check(){signal input x;var t=Child()(in<==x);\
         signal output y,w;y<==t;w<==1;}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    let w = assigned_path(&hir, definition, "w");
    assert!(facts.incidence(&x).unavailable().is_some());
    assert_eq!(facts.incidence(&w).certified(), Some(&Incidence::Must));
}

#[test]
fn opaque_function_equality_blocks_only_its_argument() {
    for equality in ["F(x)===1", "1===F(x)"] {
        let source = format!(
            "function F(a){{return a;}} template Check(){{signal input x;signal output z;\
             {equality};z<==1;}}"
        );
        let (hir, definition) = fixture(&source);
        let cfg = build_cfg(&hir, definition).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let facts = analyze(&hir, &cfg, &field, None).unwrap();
        let x = expression_path(&hir, "x", 0);
        let z = assigned_path(&hir, definition, "z");
        assert!(facts.incidence(&x).unavailable().is_some());
        assert_eq!(facts.incidence(&z).certified(), Some(&Incidence::Must));
        assert_eq!(
            cfg.nodes()
                .iter()
                .filter_map(|id| cfg.node(*id))
                .filter(|node| matches!(node.kind, CfgNodeKind::Constraint { .. }))
                .count(),
            1
        );
    }
}

#[test]
fn no_argument_function_equality_does_not_touch_unrelated_signal() {
    let (hir, definition) = fixture(
        "function F(){return 1;} template Check(){signal input x;var t=x;signal output z;\
         F()===1;z<==1;}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    let z = assigned_path(&hir, definition, "z");
    assert_eq!(facts.incidence(&x).certified(), Some(&Incidence::Zero));
    assert_eq!(facts.incidence(&z).certified(), Some(&Incidence::Must));
}

#[test]
fn unresolved_witness_call_never_generates_a_constraint() {
    let (hir, definition) = fixture(
        "function F(a){return a;} template Check(){signal input x;signal output y;y<--F(x);}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    assert_eq!(facts.incidence(&x).certified(), Some(&Incidence::Zero));
    assert!(cfg
        .nodes()
        .iter()
        .all(|id| { !matches!(cfg.node(*id).unwrap().kind, CfgNodeKind::Constraint { .. }) }));
}

#[test]
fn anonymous_constrained_input_under_witness_assignment_blocks_its_source() {
    let (hir, definition) = fixture(
        "template Child(){signal input in;signal output out;out<==in;} \
         template Check(){signal input x;signal output y,z;y<--Child()(in<==x);z<==1;}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    let z = assigned_path(&hir, definition, "z");
    assert!(facts.incidence(&x).unavailable().is_some());
    assert_eq!(facts.incidence(&z).certified(), Some(&Incidence::Must));
}

#[test]
fn signed_field_comparison_selects_the_negative_branch() {
    let (hir, definition) =
        fixture("template Check(){signal output y; if(-1<0){y<==1;}else{y<--1;}}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let DefinitionRef::Template(id) = definition else { panic!("template") };
    let body = hir.block(hir.template(id).unwrap().body).unwrap();
    let Some(Effect::If { then_block, .. }) = body.effects.last() else { panic!("if") };
    let then_block = hir.block(*then_block).unwrap();
    let Some(Effect::ConstraintAssignment { target, .. }) = then_block.effects.first() else {
        panic!("constraint")
    };
    assert_eq!(facts.incidence(target).certified(), Some(&Incidence::Must));
}

#[test]
fn two_exact_array_dependencies_do_not_mention_a_third_element() {
    let (hir, definition) = fixture(
        "template Check(){signal input a[3]; var t=a[0]; \
         if(0 << 513){t=a[0];}else{t=a[1];} \
         signal output y; y<==t; signal output z; z<--a[2];}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let third = hir
        .expressions()
        .iter()
        .find_map(|expression| {
            let ExprKind::Access(path) = &expression.kind else { return None };
            let third = path.steps.iter().any(|step| match step {
                AccessStep::Index { index: ArrayIndex::Constant(index), .. } => index == "2",
                AccessStep::Index { .. } | AccessStep::Port { .. } | AccessStep::Tag { .. } => {
                    false
                }
            });
            third.then_some(path)
        })
        .unwrap();
    assert_eq!(facts.incidence(third).certified(), Some(&Incidence::Zero));
}

#[test]
fn deferred_control_blocks_branch_constraints_but_not_independent_sibling() {
    let (hir, definition) = fixture(
        "template Check(n){signal output x; signal output y; signal output z; \
         if(n){x <== 1;}else{x <== 2;} y <== 3; z <-- x;}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    let y = assigned_path(&hir, definition, "y");
    assert!(facts.incidence(&x).unavailable().is_some());
    assert_eq!(facts.incidence(&y).certified(), Some(&Incidence::Must));
}

#[test]
fn loop_backedge_cannot_hide_deferred_control_dependence() {
    let (hir, definition) = fixture(
        "template Check(n){signal output y; for(var i=0;i<17;i++){i=16; if(n){y <== 7;}} \
         y <-- 1;}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let y = last_assigned_path(&hir, definition, "y");
    assert!(facts.incidence(&y).unavailable().is_some_and(|blockers| {
        blockers.iter().any(|blocker| matches!(blocker, FactBlocker::DeferredControl(_)))
    }));
}

#[test]
fn symbolic_index_may_alias_but_compile_time_index_is_exact() {
    let (hir, definition) =
        fixture("template Check() { signal input i; signal output a[2]; a[i] <== 1; a[0] <-- 2; }");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = last_assigned_path(&hir, definition, "a");
    assert_eq!(facts.incidence(&path).certified(), Some(&Incidence::May));

    let (hir, definition) =
        fixture("template Check() { var i = 0; signal output a[2]; a[i] <== 1; a[0] <-- 2; }");
    let cfg = build_cfg(&hir, definition).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = last_assigned_path(&hir, definition, "a");
    assert_eq!(facts.incidence(&path).certified(), Some(&Incidence::Must));
}

#[test]
fn field_equal_negative_and_prime_minus_one_share_a_fixed_value() {
    let field = FieldContext::for_curve(Curve::Bn254);
    let p_minus_one = field.canonical((-1).into());
    let (hir, definition) = fixture("template Check() { signal output y; y <== -1; }");
    let cfg = build_cfg(&hir, definition).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = assigned_path(&hir, definition, "y");
    assert_eq!(facts.constraint_fixed(&path).certified(), Some(&Some(p_minus_one)));
}

#[test]
fn explicit_equality_orientations_use_canonical_field_values() {
    let field = FieldContext::for_curve(Curve::Bn254);
    let expected = Some(field.canonical((-1).into()));
    let p_minus_one =
        "21888242871839275222246405745257275088548364400416034343698204186575808495616";
    for source in [
        "template Check(){signal input x; x === -1; }".to_owned(),
        "template Check(){signal input x; -1 === x; }".to_owned(),
        format!("template Check(){{signal input x; x === {p_minus_one};}}"),
    ] {
        let (hir, definition) = fixture(&source);
        let cfg = build_cfg(&hir, definition).unwrap();
        let facts = analyze(&hir, &cfg, &field, None).unwrap();
        let x = expression_path(&hir, "x", 0);
        assert_eq!(facts.constraint_fixed(&x).certified(), Some(&expected), "{source}");
    }
    let (hir, definition) = fixture("template Check(){signal output x; x <-- -1;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = assigned_path(&hir, definition, "x");
    assert_eq!(facts.constraint_fixed(&x).certified(), Some(&None));
}

#[test]
fn unrelated_external_component_does_not_poison_local_constraint() {
    let (hir, definition) = fixture(
        "template Child() { signal input a; } template Check() { component c = Child(); signal output y; y <== 7; }",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = assigned_path(&hir, definition, "y");
    assert_eq!(facts.incidence(&path).certified(), Some(&Incidence::Must));
}

#[test]
fn aggregate_array_and_bus_constraints_cannot_certify_child_zero() {
    let field = FieldContext::for_curve(Curve::Bn254);
    let (hir, definition) = fixture(
        "template Check() { signal input a[2]; signal output b[2]; b <== a; \
         signal output z; z <-- b[0]; }",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    assert!(facts.incidence(&expression_path(&hir, "b", 1)).unavailable().is_some());

    let (hir, definition) = fixture(
        "bus B(){signal x;} template Check(){B input source; B output target; \
         target <== source; signal output z; z <-- target.x;}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    assert!(facts.incidence(&expression_path(&hir, "target", 1)).unavailable().is_some());
}

#[test]
fn aggregate_equality_does_not_hide_child_constraint() {
    let (hir, definition) = fixture(
        "template Check(){signal input a[2]; signal input b[2]; a === b; \
         signal output z; z <-- a[0];}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    assert!(facts.incidence(&expression_path(&hir, "a", 1)).unavailable().is_some());
}

#[test]
fn aggregate_values_do_not_certify_scalar_range_or_degree() {
    let (hir, definition) = fixture(
        "bus B(){signal x;} template Check(){B input source; B output target; target <== source;}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let aggregate = hir
        .expressions()
        .iter()
        .find_map(|expression| {
            let ExprKind::Access(path) = &expression.kind else { return None };
            hir.symbol(path.root)
                .is_some_and(|symbol| symbol.name == "source")
                .then_some(expression.id)
        })
        .unwrap();
    assert!(facts.range(aggregate).unavailable().is_some());
    assert!(facts.degree(aggregate).unavailable().is_some());

    let (hir, definition) =
        fixture("template Check(){signal input a[2]; signal output b[2]; b <== a;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let aggregate = hir
        .expressions()
        .iter()
        .find_map(|expression| {
            let ExprKind::Access(path) = &expression.kind else { return None };
            hir.symbol(path.root).is_some_and(|symbol| symbol.name == "a").then_some(expression.id)
        })
        .unwrap();
    assert!(facts.range(aggregate).unavailable().is_some());
    assert!(facts.degree(aggregate).unavailable().is_some());
}

#[test]
fn constraint_dependencies_follow_intermediate_variables() {
    let (hir, definition) =
        fixture("template Check(){signal input x; var t=x; signal output y; y <== t;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    assert_eq!(facts.incidence(&x).certified(), Some(&Incidence::May));

    let (hir, definition) =
        fixture("template Check(){signal input x; var t=x; signal output y; y <-- t;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    assert_eq!(facts.incidence(&x).certified(), Some(&Incidence::Zero));
}

#[test]
fn overwritten_variable_does_not_keep_stale_constraint_dependencies() {
    let (hir, definition) =
        fixture("template Check(){signal input x; var t=x; t=0; signal output y; y <== t;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    let t = hir
        .expressions()
        .iter()
        .find_map(|expression| {
            let ExprKind::Access(path) = &expression.kind else { return None };
            hir.symbol(path.root).is_some_and(|symbol| symbol.name == "t").then_some(expression.id)
        })
        .unwrap();
    assert_eq!(facts.incidence(&x).certified(), Some(&Incidence::Zero));
    assert_eq!(facts.dependencies(t).certified().map(BTreeSet::is_empty), Some(true));
}

#[test]
fn local_variable_degree_follows_its_reaching_definition() {
    let (hir, definition) =
        fixture("template Check(){signal input x; var t=x; signal output y; y <== t;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let t = hir
        .expressions()
        .iter()
        .find_map(|expression| {
            let ExprKind::Access(path) = &expression.kind else { return None };
            hir.symbol(path.root).is_some_and(|symbol| symbol.name == "t").then_some(expression.id)
        })
        .unwrap();
    assert_eq!(
        facts.degree(t).certified(),
        Some(&circomspect_program_analysis::hir_facts::Degree::Linear)
    );
}

#[test]
fn backward_liveness_tracks_reads_before_assignment() {
    let (hir, definition) = fixture("function Check(){var x=1; var y=x; return y;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    let read = cfg
        .nodes()
        .iter()
        .copied()
        .find(|node| match &cfg.node(*node).unwrap().kind {
            CfgNodeKind::Evaluate(id) => {
                let Some(ExprKind::Access(path)) = hir.expression(*id).map(|expr| &expr.kind)
                else {
                    return false;
                };
                path.root == x.root
            }
            _ => false,
        })
        .unwrap();
    assert_eq!(facts.live_before(read, &x).certified(), Some(&true));
}

#[test]
fn template_output_is_live_at_exit_while_unused_local_is_dead() {
    let (hir, definition) = fixture("template Check(){var t=7; signal output y; y <-- 7;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let output = assigned_path(&hir, definition, "y");
    let t = hir.symbols().iter().find(|symbol| symbol.name == "t").unwrap();
    let local_assignment = cfg
        .nodes()
        .iter()
        .copied()
        .find(|id| {
            let Some(node) = cfg.node(*id) else { return false };
            matches!(&node.kind, CfgNodeKind::Assignment { target, .. } if target.root == t.id)
        })
        .unwrap();
    let output_assignment = cfg
        .nodes()
        .iter()
        .copied()
        .find(|id| {
            let Some(node) = cfg.node(*id) else { return false };
            matches!(&node.kind, CfgNodeKind::Witness { target, .. } if target.root == output.root)
        })
        .unwrap();
    assert_eq!(facts.live_before(output_assignment, &output).certified(), Some(&true));
    let DefinitionRef::Template(id) = definition else { panic!("template fixture") };
    let body = hir.block(hir.template(id).unwrap().body).unwrap();
    let local = body
        .effects
        .iter()
        .find_map(|effect| match effect {
            Effect::VariableAssignment { target, .. } if target.root == t.id => {
                Some(target.clone())
            }
            _ => None,
        })
        .unwrap();
    assert_eq!(facts.live_before(local_assignment, &local).certified(), Some(&false));
}

#[test]
fn cross_project_cfg_is_rejected_before_any_fact_can_certify() {
    let (first, definition) = fixture("template Check(){signal output y; y <== 7;}");
    let (other, _) = fixture("template Check(){signal output y; y <-- 7;}");
    let cfg = build_cfg(&first, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    assert!(matches!(analyze(&other, &cfg, &field, None), Err(AnalysisError::ForeignProject)));
}

#[test]
fn query_paths_from_other_definitions_or_projects_are_unavailable() {
    let directory = std::env::temp_dir()
        .join(format!("circomspect-phase4-foreign-query-{}", std::process::id()));
    fs::create_dir_all(&directory).unwrap();
    let source = directory.join("case.circom");
    fs::write(
        &source,
        "template T(){signal output y; y<==1;} template U(){signal output z; z<--2;}",
    )
    .unwrap();
    let loaded = load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let first = lift_project(&loaded).hir;
    let second = lift_project(&loaded).hir;
    let cfg = build_cfg(&first, first.definition("T").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&first, &cfg, &field, None).unwrap();
    let local = assigned_path(&first, first.definition("T").unwrap(), "y");
    let other = assigned_path(&first, first.definition("U").unwrap(), "z");
    let foreign = assigned_path(&second, second.definition("T").unwrap(), "y");
    assert_eq!(facts.incidence(&local).certified(), Some(&Incidence::Must));
    assert!(facts
        .incidence(&other)
        .unavailable()
        .is_some_and(|blockers| blockers.contains(&FactBlocker::ForeignDefinition)));
    assert!(facts
        .incidence(&foreign)
        .unavailable()
        .is_some_and(|blockers| blockers.contains(&FactBlocker::ForeignQuery)));

    let mut forged = local.clone();
    forged.terminal = foreign.root;
    assert!(facts.incidence(&forged).unavailable().is_some());
    forged.terminal = other.root;
    assert!(facts.incidence(&forged).unavailable().is_some());
    forged = local.clone();
    forged.steps.push(AccessStep::Index {
        index: ArrayIndex::Symbolic(second.expressions()[0].id),
        span: local.span,
    });
    assert!(facts.incidence(&forged).unavailable().is_some());
}

#[test]
fn foreign_symbolic_index_cannot_be_grafted_onto_a_local_root() {
    let directory = std::env::temp_dir()
        .join(format!("circomspect-phase4-foreign-index-{}", std::process::id()));
    fs::create_dir_all(&directory).unwrap();
    let source = directory.join("case.circom");
    fs::write(
        &source,
        "template T(){signal input a[2];signal output y;y<==a[0];} \
         template U(){signal input b[2];var i=0;signal output z;z<--b[i];}",
    )
    .unwrap();
    let loaded = load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let hir = lift_project(&loaded).hir;
    let cfg = build_cfg(&hir, hir.definition("T").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let mut grafted = expression_path(&hir, "a", 1);
    let foreign = expression_path(&hir, "b", 1);
    grafted.steps = foreign.steps;
    assert!(facts
        .incidence(&grafted)
        .unavailable()
        .is_some_and(|blockers| { blockers.contains(&FactBlocker::ForeignQuery) }));
}

#[test]
fn known_false_branch_does_not_block_independent_constraint_fact() {
    let directory = std::env::temp_dir()
        .join(format!("circomspect-phase4-unreachable-opaque-{}", std::process::id()));
    fs::create_dir_all(&directory).unwrap();
    let source = directory.join("case.circom");
    fs::write(&source, "template Check(){signal output y; if(0){y<==Missing();} y<==1;}").unwrap();
    let loaded = load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty());
    let hir = lifted.hir;
    let definition = hir.definition("Check").unwrap();
    let cfg = build_cfg(&hir, definition).unwrap();
    assert!(cfg.nodes().iter().filter_map(|id| cfg.node(*id)).any(|node| {
        if let CfgNodeKind::Opaque(_) = &node.kind {
            return true;
        }
        false
    }));
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let y = last_assigned_path(&hir, definition, "y");
    assert_eq!(facts.incidence(&y).certified(), Some(&Incidence::Must));
}

#[test]
fn selected_curve_changes_canonical_field_value() {
    let goldilocks = FieldContext::for_curve(Curve::Goldilocks);
    let bn254 = FieldContext::for_curve(Curve::Bn254);
    assert_ne!(goldilocks.canonical((-1).into()), bn254.canonical((-1).into()));
    assert_eq!(goldilocks.curve(), &Curve::Goldilocks);
}

#[test]
fn exhausted_budget_can_leave_an_independent_zero_certified() {
    let (hir, definition) =
        fixture("template Check(){signal output y; y <-- 1; signal output x; x <== 7;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, Some(1)).unwrap();
    let y = assigned_path(&hir, definition, "y");
    let x = assigned_path(&hir, definition, "x");
    assert_eq!(facts.incidence(&y).certified(), Some(&Incidence::Zero));
    assert!(facts.incidence(&x).unavailable().is_some());
}

#[test]
fn deferred_branch_values_stay_unavailable_even_when_both_arms_agree() {
    let field = FieldContext::for_curve(Curve::Bn254);
    for alternative in ["1", "2"] {
        let source = format!(
            "function Check(n){{var x=0; if(n){{x=1;}}else{{x={alternative};}} return x;}}"
        );
        let (hir, definition) = fixture(&source);
        let cfg = build_cfg(&hir, definition).unwrap();
        let facts = analyze(&hir, &cfg, &field, None).unwrap();
        let DefinitionRef::Function(id) = definition else { panic!("function fixture") };
        let body = hir.block(hir.function(id).unwrap().body).unwrap();
        let expression = body.expressions()[0];
        assert!(facts.range(expression).unavailable().is_some(), "{source}");
    }
}

#[test]
fn deferred_guard_blocks_only_values_derived_from_its_assignments() {
    let (hir, definition) = fixture(
        "function Check(n){var clean=7; var copied=clean; var x=0; \
         if(n){x=1;}else{x=1;} return x;}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let clean = hir
        .expressions()
        .iter()
        .find_map(|expression| {
            let ExprKind::Access(path) = &expression.kind else { return None };
            hir.symbol(path.root)
                .is_some_and(|symbol| symbol.name == "clean")
                .then_some(expression.id)
        })
        .unwrap();
    let x = hir
        .expressions()
        .iter()
        .find_map(|expression| {
            let ExprKind::Access(path) = &expression.kind else { return None };
            hir.symbol(path.root).is_some_and(|symbol| symbol.name == "x").then_some(expression.id)
        })
        .unwrap();
    assert_eq!(facts.range(clean).certified(), Some(&Range::Exact(field.canonical(7.into()))));
    assert!(facts.range(x).unavailable().is_some());
}

#[test]
fn returning_arm_keeps_following_value_guard_dependent() {
    let (hir, definition) = fixture("function Check(n){var x=0; if(n){return 0;} x=1; return x;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = hir
        .expressions()
        .iter()
        .find_map(|expr| {
            let ExprKind::Access(path) = &expr.kind else { return None };
            hir.symbol(path.root).is_some_and(|symbol| symbol.name == "x").then_some(expr.id)
        })
        .unwrap();
    assert!(facts.range(x).unavailable().is_some());
}

#[test]
fn deferred_ternary_does_not_certify_even_matching_arm_values() {
    let (hir, definition) = fixture("function Check(n){return n ? 1 : 1;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let expression = hir
        .expressions()
        .iter()
        .find_map(|expr| match &expr.kind {
            ExprKind::Ternary { .. } => Some(expr.id),
            _ => None,
        })
        .unwrap();
    assert!(facts.range(expression).unavailable().is_some());
}

#[test]
fn parameter_with_deferred_shape_has_no_scalar_range_or_degree() {
    let (hir, definition) = fixture("function Check(n){if(n){return 1;} return n;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let n = hir
        .expressions()
        .iter()
        .find_map(|expr| {
            let ExprKind::Access(path) = &expr.kind else { return None };
            hir.symbol(path.root).is_some_and(|symbol| symbol.name == "n").then_some(expr.id)
        })
        .unwrap();
    assert!(facts.range(n).unavailable().is_some());
    assert!(facts.degree(n).unavailable().is_some());
}

#[test]
fn fixed_bound_loop_canonicalizes_induction_indices() {
    let (hir, definition) = fixture(
        "template Check(){var i=0; signal output y[2]; \
         for(var j=0;j<2;j++){y[j] <== i;} signal output z; z <-- y[0];}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let y = expression_path(&hir, "y", 1);
    assert_eq!(facts.incidence(&y).certified(), Some(&Incidence::Must));
}

#[test]
fn proven_small_for_bounds_have_exact_constraint_incidence() {
    let field = FieldContext::for_curve(Curve::Bn254);
    for (initial, bound, expected) in [
        (0, 0, Incidence::Zero),
        (0, 1, Incidence::Must),
        (0, 2, Incidence::Must),
        (1, 2, Incidence::Must),
        (2, 2, Incidence::Zero),
        (15, 16, Incidence::Must),
    ] {
        let source = format!(
            "template Check(){{signal output y; for(var j={initial};j<{bound};j++){{y <== 7;}} y <-- 2;}}"
        );
        let (hir, definition) = fixture(&source);
        let cfg = build_cfg(&hir, definition).unwrap();
        let facts = analyze(&hir, &cfg, &field, None).unwrap();
        let y = last_assigned_path(&hir, definition, "y");
        assert_eq!(facts.incidence(&y).certified(), Some(&expected), "{source}");
    }
}

#[test]
fn loop_body_that_changes_induction_variable_is_not_unrolled() {
    let (hir, definition) = fixture(
        "template Check(){signal output y[2]; for(var j=0;j<2;j++){j++; y[j] <== 7;} \
         signal output z; z <-- y[1];}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let y = expression_path(&hir, "y", 1);
    assert_ne!(facts.incidence(&y).certified(), Some(&Incidence::Must));
}
