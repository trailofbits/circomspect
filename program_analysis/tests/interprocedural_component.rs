use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::{analyze, FieldContext};
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ProjectSummaries, SummaryBlocker,
};
use parser::hir::{lift_project, DefinitionRef, LiftedProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;
use std::fs;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-component-summary-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

#[test]
fn exact_array_instances_keep_distinct_parameterized_output_values() {
    let lifted = fixture(concat!(
        "template Child(n){signal output out;if(n){out<==1;}else{out<==0;}} ",
        "template Parent(){component c[2];c[0]=Child(0);c[1]=Child(1);}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let output = lifted.hir.template(child).unwrap().ports[0];
    let component = lifted.hir.components()[0].id;
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let calls = provider.graph().calls_from(CallOwner::Definition(parent));
    assert_eq!(calls.len(), 2);
    let field = FieldContext::for_curve(Curve::Bn254);
    for (index, expected) in [(0, 0), (1, 1)] {
        let handle = facts.component_output_handle(component, &[index], output, &[]).unwrap();
        let CallReachability::Reachable(call) =
            provider.graph().reachable_call(calls[index].id(), &facts)
        else {
            panic!("exact call must be reachable")
        };
        let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
        let applied = applied.certified().unwrap_or_else(|| panic!("{:?}", applied.unavailable()));
        assert_eq!(applied.port_summary().fixed_value(), Some(&field.canonical(expected.into())));
        assert_eq!(
            applied.callee_evidence().context().definition(),
            DefinitionRef::Template(child)
        );
    }
}

#[test]
fn a_reachable_call_cannot_borrow_another_instance_output() {
    let lifted = fixture(concat!(
        "template Child(n){signal output out;if(n){out<==1;}else{out<==0;}} ",
        "template Parent(){component c[2];c[0]=Child(0);c[1]=Child(1);}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[0];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[1], output, &[]).unwrap();
    let calls = provider.graph().calls_from(CallOwner::Definition(parent));
    let CallReachability::Reachable(first) = provider.graph().reachable_call(calls[0].id(), &facts)
    else {
        panic!("first call must be reachable")
    };
    assert!(provider
        .apply_component_output(&facts, &scope, &first, &handle)
        .unavailable()
        .unwrap()
        .contains(&SummaryBlocker::WrongInstance));

    let field = FieldContext::for_curve(Curve::Bn254);
    let unbound = analyze(&lifted.hir, &cfg, &field, None).unwrap();
    let unbound_handle =
        unbound.component_output_handle(lifted.hir.components()[0].id, &[0], output, &[]).unwrap();
    assert!(provider
        .apply_component_output(&facts, &scope, &first, &unbound_handle)
        .unavailable()
        .unwrap()
        .contains(&SummaryBlocker::WrongContext));
}

#[test]
fn duplicate_instantiation_cannot_double_apply_one_child_summary() {
    let lifted = fixture(concat!(
        "template Child(){signal output out;out<==1;} ",
        "template Parent(){component c=Child();c=Child();}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[0];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
    let calls = provider.graph().calls_from(CallOwner::Definition(parent));
    assert_eq!(calls.len(), 2);
    let CallReachability::Reachable(first) = provider.graph().reachable_call(calls[0].id(), &facts)
    else {
        panic!("first call must be reachable")
    };
    assert!(provider
        .apply_component_output(&facts, &scope, &first, &handle)
        .unavailable()
        .unwrap()
        .contains(&SummaryBlocker::DuplicateInstance));
}

#[test]
fn symbolic_instance_index_cannot_borrow_an_exact_output_handle() {
    let lifted = fixture(concat!(
        "template Child(){signal output out;out<==1;} ",
        "template Parent(){var i=0;component c[2];c[i]=Child();}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[0];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[0], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("symbolic target still has a reachable call")
    };
    assert!(provider
        .apply_component_output(&facts, &scope, &call, &handle)
        .unavailable()
        .unwrap()
        .contains(&SummaryBlocker::SymbolicInstance));
}

#[test]
fn unknown_template_argument_keeps_output_application_unavailable() {
    let lifted = fixture(concat!(
        "template Child(n){signal output out;if(n){out<==1;}else{out<==0;}} ",
        "template Parent(n){component c=Child(n);}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[0];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("source call remains reachable")
    };
    assert!(provider
        .apply_component_output(&facts, &scope, &call, &handle)
        .unavailable()
        .is_some());
}
