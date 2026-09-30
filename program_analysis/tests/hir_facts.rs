use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::{analyze, Fact, FieldContext, Incidence};
use parser::hir::{lower_project, AccessPath, DefinitionRef, Effect, HirProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use std::fs;

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

#[test]
fn witness_value_and_assert_do_not_prove_constraint_incidence() {
    let (hir, definition) =
        fixture("template Check() { signal output y; y <-- 7; assert(y == 7); }");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::bn254();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = assigned_path(&hir, definition, "y");
    assert_eq!(facts.incidence(&path), Fact::Certified(Incidence::Zero));
    assert_eq!(facts.constraint_fixed(&path), Fact::Certified(None));
}

#[test]
fn late_equality_revokes_zero_incidence() {
    let (hir, definition) = fixture("template Check() { signal output y; y <-- 7; y === 7; }");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::bn254();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = assigned_path(&hir, definition, "y");
    assert_eq!(facts.incidence(&path), Fact::Certified(Incidence::Must));
}

#[test]
fn constraint_assignment_generates_incidence_and_fixed_value() {
    let (hir, definition) = fixture("template Check() { signal output y; y <== 7; }");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::bn254();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = assigned_path(&hir, definition, "y");
    assert_eq!(facts.incidence(&path), Fact::Certified(Incidence::Must));
    assert_eq!(facts.constraint_fixed(&path), Fact::Certified(Some(field.canonical(7.into()))));
}

#[test]
fn exhausted_budget_never_certifies_a_provisional_zero() {
    let (hir, definition) = fixture("template Check() { signal output y; y <== 7; }");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::bn254();
    let facts = analyze(&hir, &cfg, &field, Some(1)).unwrap();
    let path = assigned_path(&hir, definition, "y");
    assert!(matches!(facts.incidence(&path), Fact::Unavailable(_)));
}

#[test]
fn branch_must_constraint_needs_proven_compile_time_choice() {
    let (hir, definition) = fixture(
        "template Check(n) { signal output y; if (n) { y <== 7; } else { y <-- 7; } y <-- 1; }",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::bn254();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = last_assigned_path(&hir, definition, "y");
    assert!(matches!(facts.incidence(&path), Fact::Unavailable(_)));

    let (hir, definition) = fixture(
        "template Check() { signal output y; if (1) { y <== 7; } else { y <-- 7; } y <-- 1; }",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = last_assigned_path(&hir, definition, "y");
    assert_eq!(facts.incidence(&path), Fact::Certified(Incidence::Must));
}

#[test]
fn symbolic_index_may_alias_but_compile_time_index_is_exact() {
    let (hir, definition) =
        fixture("template Check() { signal input i; signal output a[2]; a[i] <== 1; a[0] <-- 2; }");
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::bn254();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = last_assigned_path(&hir, definition, "a");
    assert_eq!(facts.incidence(&path), Fact::Certified(Incidence::May));

    let (hir, definition) =
        fixture("template Check() { var i = 0; signal output a[2]; a[i] <== 1; a[0] <-- 2; }");
    let cfg = build_cfg(&hir, definition).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = last_assigned_path(&hir, definition, "a");
    assert_eq!(facts.incidence(&path), Fact::Certified(Incidence::Must));
}

#[test]
fn field_equal_negative_and_prime_minus_one_share_a_fixed_value() {
    let field = FieldContext::bn254();
    let p_minus_one = field.canonical((-1).into());
    let (hir, definition) = fixture("template Check() { signal output y; y <== -1; }");
    let cfg = build_cfg(&hir, definition).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = assigned_path(&hir, definition, "y");
    assert_eq!(facts.constraint_fixed(&path), Fact::Certified(Some(p_minus_one)));
}

#[test]
fn unrelated_external_component_does_not_poison_local_constraint() {
    let (hir, definition) = fixture(
        "template Child() { signal input a; } template Check() { component c = Child(); signal output y; y <== 7; }",
    );
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::bn254();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let path = assigned_path(&hir, definition, "y");
    assert_eq!(facts.incidence(&path), Fact::Certified(Incidence::Must));
}
