// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use std::collections::BTreeSet;
use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::FieldContext;
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ComposedConstraintFixedOutput, ProjectAnalysis, SummaryBlocker,
};
use parser::hir::{lift_project, DefinitionRef, LiftedProject};
use parser::frontend::{load_sources, PortDirection, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-component-join-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

fn composed(
    source: &str,
    budget: Option<usize>,
) -> Result<ComposedConstraintFixedOutput, BTreeSet<SummaryBlocker>> {
    let lifted = fixture(source);
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let caller = provider.contexts().symbolic_root(parent).unwrap();
    let full = provider.contexts().analyze_for_evidence(&cfg, &caller, None).unwrap();
    let output = lifted
        .hir
        .template(child)
        .unwrap()
        .ports
        .iter()
        .copied()
        .find(|id| {
            lifted.hir.port(*id).is_some_and(|port| port.direction == Some(PortDirection::Output))
        })
        .unwrap();
    let handle = full.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]);
    let handle = handle.unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &full)
    else {
        panic!("Child must be reachable")
    };
    let applied = provider.apply_component_output(&full, &caller, &call, &handle);
    let applied = applied.certified().ok_or_else(|| applied.unavailable().unwrap().clone())?;
    let pending =
        budget.map(|limit| provider.contexts().analyze_for_evidence(&cfg, &caller, Some(limit)));
    let pending = pending.map(Result::unwrap);
    let facts = pending.as_ref().unwrap_or(&full);
    let result = provider.composed_constraint_fixed_output(facts, applied);
    result.certified().cloned().ok_or_else(|| result.unavailable().unwrap().clone())
}

#[test]
fn agreeing_branch_bindings_certify_one_output_value_with_both_origins() {
    let result = composed(
        concat!(
            "template Child(){signal input in;signal output out;out<==in;} ",
            "template Parent(){component c=Child();",
            "if(1 << 513){c.in<==7;}else{c.in<==7;}",
            "signal output y;y<==c.out;}"
        ),
        None,
    );
    let field = FieldContext::for_curve(Curve::Bn254);
    let proof = result.unwrap();
    assert_eq!(proof.value(), &field.canonical(7.into()));
    assert_eq!(proof.caller_inputs().len(), 2);
    assert_ne!(proof.caller_inputs()[0], proof.caller_inputs()[1]);
}

#[test]
fn differing_or_one_sided_branch_bindings_cannot_fix_output() {
    for branch in ["if(1 << 513){c.in<==7;}else{c.in<==8;}", "if(1 << 513){c.in<==7;}"] {
        let source = format!(
            "template Child(){{signal input in;signal output out;out<==in;}} \
             template Parent(){{component c=Child();{branch}signal output y;y<==c.out;}}"
        );
        assert!(composed(&source, None).is_err());
    }
}

#[test]
fn an_unproved_parameter_guard_cannot_certify_even_agreeing_bindings() {
    let result = composed(
        concat!(
            "template Child(){signal input in;signal output out;out<==in;} ",
            "template Parent(n){component c=Child();",
            "if(n){c.in<==7;}else{c.in<==7;}",
            "signal output y;y<==c.out;}"
        ),
        None,
    );
    assert!(result.is_err());
}

#[test]
fn read_before_all_inputs_and_duplicate_writes_remain_unavailable() {
    let early = composed(
        concat!(
            "template Child(){signal input a;signal input b;signal output out;out<==a;} ",
            "template Parent(){component c=Child();c.a<==7;",
            "signal output y;y<==c.out;c.b<==1;}"
        ),
        None,
    );
    assert!(early.is_err());
    let duplicate = composed(
        concat!(
            "template Child(){signal input in;signal output out;out<==in;} ",
            "template Parent(){component c=Child();c.in<==7;c.in<==7;}"
        ),
        None,
    );
    assert!(duplicate.unwrap_err().contains(&SummaryBlocker::UnsupportedContext));
    let conflicting_equality = composed(
        concat!(
            "template Child(){signal input in;signal output out;out<==in;} ",
            "template Parent(){component c=Child();c.in<==7;c.in===8;}"
        ),
        None,
    );
    assert!(conflicting_equality.is_err());
}

#[test]
fn caller_loop_and_exhausted_budget_cannot_promote_binding() {
    let looped = composed(
        concat!(
            "template Child(){signal input in;signal output out;out<==in;} ",
            "template Parent(){component c=Child();",
            "for(var i=0;i<2;i++){c.in<==7;}signal output y;y<==c.out;}"
        ),
        None,
    );
    assert!(looped.unwrap_err().contains(&SummaryBlocker::UnsupportedContext));
    let straight = concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(){component c=Child();c.in<==7;}"
    );
    assert!(composed(straight, Some(0)).is_err());
}

#[test]
fn an_unproved_array_index_cannot_fix_a_child_input() {
    let result = composed(
        concat!(
            "template Child(){signal input in;signal output out;out<==in;} ",
            "template Parent(){var values[1]=[7];component c=Child();",
            "c.in<==values[1];signal output y;y<==c.out;}"
        ),
        None,
    );
    assert!(result
        .err()
        .is_some_and(|reasons| reasons.contains(&SummaryBlocker::UnsupportedContext)));
}
#[test]
fn composing_one_output_checks_readiness_before_every_sibling_output_read() {
    for (body, expected) in [
        ("c.in<==7;signal output y;y<==c.other;", true),
        ("signal output y;y<==c.other;c.in<==7;", false),
    ] {
        let source = format!(
            "template Child(){{signal input in;signal output out;signal output other;\
             out<==in;other<==in;}}template Parent(){{component c=Child();{body}}}"
        );
        let result = composed(&source, None);
        assert_eq!(result.is_ok(), expected, "{source}: {result:?}");
    }
}
