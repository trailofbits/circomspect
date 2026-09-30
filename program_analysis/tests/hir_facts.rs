use abstract_interpretation::graph::FlowGraph;
use circomspect_program_analysis::hir_cfg::{build_cfg, CfgNodeKind};
use circomspect_program_analysis::hir_facts::{analyze, AnalysisError, FieldContext, Incidence};
use parser::hir::{lower_project, AccessPath, DefinitionRef, Effect, ExprKind, HirProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use std::fs;
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> (HirProject, DefinitionRef) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-phase4-facts-{}-{:?}",
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
    (lowered.hir, definition)
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
        .filter_map(|expression| match &expression.kind {
            ExprKind::Access(path)
                if hir.symbol(path.root).is_some_and(|symbol| symbol.name == name)
                    && path.steps.len() >= minimum_steps =>
            {
                Some(path.clone())
            }
            _ => None,
        })
        .next()
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
fn branch_must_constraint_needs_proven_compile_time_choice() {
    let (hir, definition) = fixture(
        "template Check(n) { signal output y; if (n) { y <== 7; } else { y <-- 7; } y <-- 1; }",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = last_assigned_path(&hir, definition, "y");
    assert!(facts.incidence(&path).unavailable().is_some());

    let (hir, definition) = fixture(
        "template Check() { signal output y; if (1) { y <== 7; } else { y <-- 7; } y <-- 1; }",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = last_assigned_path(&hir, definition, "y");
    assert_eq!(facts.incidence(&path).certified(), Some(&Incidence::Must));
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
fn constraint_dependencies_follow_intermediate_variables() {
    let (hir, definition) =
        fixture("template Check(){signal input x; var t=x; signal output y; y <== t;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    assert_ne!(facts.incidence(&x).certified(), Some(&Incidence::Zero));

    let (hir, definition) =
        fixture("template Check(){signal input x; var t=x; signal output y; y <-- t;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let x = expression_path(&hir, "x", 0);
    assert_eq!(facts.incidence(&x).certified(), Some(&Incidence::Zero));
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
fn cross_project_cfg_is_rejected_before_any_fact_can_certify() {
    let (first, definition) = fixture("template Check(){signal output y; y <== 7;}");
    let (other, _) = fixture("template Check(){signal output y; y <-- 7;}");
    let cfg = build_cfg(&first, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    assert!(matches!(analyze(&other, &cfg, &field, None), Err(AnalysisError::ForeignProject)));
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
fn opaque_symbolic_branch_blocks_a_provisional_exact_value() {
    let (hir, definition) = fixture("function Check(n){var x=0; if(n){x=1;}else{x=2;} return x;}");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let DefinitionRef::Function(id) = definition else { panic!("function fixture") };
    let body = hir.block(hir.function(id).unwrap().body).unwrap();
    let expression = body.expressions()[0];
    assert!(facts.range(expression).unavailable().is_some());
}

#[test]
fn loop_update_keeps_must_constraint_unavailable() {
    let (hir, definition) = fixture(
        "template Check(){var i=0; signal output y[2]; \
         for(var j=0;j<2;j++){y[j] <== i;} signal output z; z <-- y[0];}",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let y = expression_path(&hir, "y", 1);
    assert!(facts.incidence(&y).unavailable().is_some());
}
