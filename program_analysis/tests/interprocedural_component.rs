use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::{
    analyze, FactBlocker, FieldContext, Incidence, WitnessWriteIssue,
};
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, CallerOutputRead, ProjectSummaries, SummaryBlocker, SummaryFact,
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

fn output_read(source: &str, instance: usize) -> SummaryFact<CallerOutputRead> {
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[0];
    let handle = facts
        .component_output_handle(lifted.hir.components()[0].id, &[instance], output, &[])
        .unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[instance];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("component call must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
    provider.caller_output_read(&facts, applied.certified().unwrap())
}

#[test]
fn nested_exact_output_access_is_a_caller_read() {
    let read = output_read(
        concat!(
            "template Child(){signal output out;out<==1;} ",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
            "signal output y;y<==c[0].out+1;}"
        ),
        0,
    );
    assert_eq!(read.certified().unwrap().read_origins().len(), 1);
}

#[test]
fn an_independent_opaque_call_does_not_hide_an_exact_read() {
    let read = output_read(
        concat!(
            "template Child(){signal output out;out<==1;} ",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
            "signal output y;y<==c[0].out;var t=Missing();}"
        ),
        0,
    );
    assert_eq!(read.certified().unwrap().read_origins().len(), 1);
}

#[test]
fn sibling_output_cannot_borrow_another_instances_read() {
    let read = output_read(
        concat!(
            "template Child(){signal output out;out<==1;} ",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
            "signal output y;y<==c[0].out;}"
        ),
        1,
    );
    assert!(read.certified().is_none());
}

#[test]
fn symbolic_output_index_cannot_prove_an_exact_read() {
    let read = output_read(
        concat!(
            "template Child(){signal output out;out<==1;} ",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
            "signal input i;signal output y;y<==c[i].out;}"
        ),
        0,
    );
    assert!(read.certified().is_none());
}

#[test]
fn opaque_expression_cannot_prove_an_output_read() {
    let read = output_read(
        concat!(
            "template Child(){signal output out;out<==1;} ",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
            "signal output y;y<==c[0].out+Missing();}"
        ),
        0,
    );
    assert!(read.certified().is_none());
}

#[test]
fn statically_pruned_output_read_is_not_observed() {
    let read = output_read(
        concat!(
            "template Child(){signal output out;out<==1;} ",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
            "signal output y;if(0){y<==c[0].out;}else{y<==1;}}"
        ),
        0,
    );
    assert!(read.certified().is_none());
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

#[test]
fn checked_input_relation_agrees_with_direct_inline_output() {
    let lifted = fixture(concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(){component c=Child();c.in<==7;} ",
        "template Inline(){signal output out;out<==7;}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let DefinitionRef::Template(inline) = lifted.hir.definition("Inline").unwrap() else {
        panic!("Inline must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[1];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("child call must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
    let applied = applied.certified().unwrap();
    assert_eq!(applied.port_summary().fixed_value(), None);

    let composed = provider.composed_constraint_fixed_output(&facts, applied);
    let inline_context = provider.symbolic_context_for(DefinitionRef::Template(inline)).unwrap();
    let inline_output = lifted.hir.template(inline).unwrap().ports[0];
    let direct = provider.template_port(inline, &inline_context, inline_output);
    assert_eq!(
        composed.certified().map(|item| item.value()),
        direct.certified().unwrap().fixed_value(),
        "{:?}",
        composed.unavailable()
    );
}

#[test]
fn witness_only_input_does_not_fix_child_output() {
    let lifted = fixture(concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(){signal input x;component c=Child();c.in<--x;",
        "signal output y;y<==c.out;}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let DefinitionRef::Template(parent_id) = parent else { panic!("Parent must be a template") };
    let x = facts.port_handle(lifted.hir.template(parent_id).unwrap().ports[0], &[]).unwrap();
    assert_eq!(facts.incidence_handle(&x).certified(), Some(&Incidence::Zero));
    let output = lifted.hir.template(child).unwrap().ports[1];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("child call must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
    assert!(provider
        .composed_constraint_fixed_output(&facts, applied.certified().unwrap())
        .unavailable()
        .is_some());
}

#[test]
fn repeated_instances_compose_only_their_own_checked_inputs() {
    let lifted = fixture(concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
        "c[0].in<==3;c[1].in<==5;}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[1];
    let calls = provider.graph().calls_from(CallOwner::Definition(parent));
    let field = FieldContext::for_curve(Curve::Bn254);
    let mut certificates = Vec::new();
    for (index, expected) in [(0, 3), (1, 5)] {
        let handle = facts
            .component_output_handle(lifted.hir.components()[0].id, &[index], output, &[])
            .unwrap();
        let CallReachability::Reachable(call) =
            provider.graph().reachable_call(calls[index].id(), &facts)
        else {
            panic!("component call must be reachable")
        };
        let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
        let value = provider.composed_constraint_fixed_output(&facts, applied.certified().unwrap());
        assert_eq!(
            value.certified().map(|item| item.value()),
            Some(&field.canonical(expected.into()))
        );
        let certificate = value.certified().unwrap();
        assert_eq!(certificate.applied_port().handle(), &handle);
        assert_eq!(certificate.applied_port().caller_evidence(), &scope);
        assert_eq!(certificate.applied_port().callee_evidence().context().arguments(), &[]);
        certificates.push(certificate.clone());
    }
    assert_ne!(certificates[0].applied_port().handle(), certificates[1].applied_port().handle());
}

#[test]
fn duplicate_and_missing_input_bindings_cannot_fix_an_output() {
    for (assignments, expected) in [
        ("c.in<==1;c.in<==2;", SummaryBlocker::UnsupportedContext),
        ("", SummaryBlocker::MissingInputBinding),
    ] {
        let source = format!(
            "template Child(){{signal input in;signal output out;out<==in;}} \
             template Parent(){{component c=Child();{assignments}}}"
        );
        let lifted = fixture(&source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let parent = lifted.hir.definition("Parent").unwrap();
        let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
            panic!("Child must be a template")
        };
        let cfg = build_cfg(&lifted.hir, parent).unwrap();
        let scope = provider.symbolic_root(parent).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
        let output = lifted.hir.template(child).unwrap().ports[1];
        let handle =
            facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
        let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
        else {
            panic!("component call must be reachable")
        };
        let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
        let result = match applied.certified() {
            Some(applied) => provider.composed_constraint_fixed_output(&facts, applied),
            None => {
                assert!(applied.unavailable().unwrap().contains(&expected));
                continue;
            }
        };
        assert!(result.unavailable().unwrap().contains(&expected));
    }
}

#[test]
fn a_may_reachable_branch_instantiation_does_not_fix_an_output() {
    let lifted = fixture(concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(){component c;if(1 << 1){c=Child();c.in<==7;}}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[1];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("branch call may be reachable")
    };
    let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
    assert!(provider
        .composed_constraint_fixed_output(&facts, applied.certified().unwrap())
        .unavailable()
        .is_some());
}

#[test]
fn disagreeing_branch_input_bindings_cannot_fix_an_output() {
    let lifted = fixture(concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(){component c=Child();",
        "if(1 << 1){c.in<==7;}else{c.in<==8;}}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[1];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("instantiation must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
    assert!(provider
        .composed_constraint_fixed_output(&facts, applied.certified().unwrap())
        .certified()
        .is_none());
}

#[test]
fn unrelated_branch_preserves_the_later_checked_input_value() {
    let lifted = fixture(concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(){component c=Child();if(1 << 1){log(1);}",
        "c.in<==7;}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[1];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("instantiation must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
    let result = provider.composed_constraint_fixed_output(&facts, applied.certified().unwrap());
    let expected = FieldContext::for_curve(Curve::Bn254).canonical(7.into());
    assert_eq!(result.certified().map(|proof| proof.value()), Some(&expected));
}

#[test]
fn equality_without_output_witness_is_not_promoted_as_a_value_write() {
    let lifted = fixture(concat!(
        "template Child(){signal input in;signal output out;out===in;} ",
        "template Parent(){component c=Child();c.in<==7;}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let child_context = provider.symbolic_context_for(DefinitionRef::Template(child)).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[1];
    assert!(provider
        .template_port_witnesses(child, &child_context, output)
        .certified()
        .is_some_and(Vec::is_empty));
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("component call must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
    assert!(provider
        .composed_constraint_fixed_output(&facts, applied.certified().unwrap())
        .unavailable()
        .is_some());
}

#[test]
fn nested_output_read_before_input_binding_blocks_composition() {
    let lifted = fixture(concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(){component c=Child();signal output y;",
        "y<==c.out+1;c.in<==7;}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[1];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("component call must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
    assert!(provider
        .composed_constraint_fixed_output(&facts, applied.certified().unwrap())
        .unavailable()
        .is_some());
}

#[test]
fn every_required_child_input_must_precede_the_output_read() {
    let lifted = fixture(concat!(
        "template Child(){signal input a;signal input b;signal output out;out<==a;} ",
        "template Parent(){component c=Child();c.a<==7;signal output y;",
        "y<==c.out;c.b<==1;}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[2];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("component call must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
    assert!(provider
        .composed_constraint_fixed_output(&facts, applied.certified().unwrap())
        .unavailable()
        .is_some());
}

#[test]
fn opaque_competing_input_write_blocks_a_fixed_output() {
    let lifted = fixture(concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(){component c=Child();c.in<==7;c.in<==Missing();}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[1];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("component call must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
    assert!(applied.certified().is_some(), "{:?}", applied.unavailable());
    assert!(provider
        .composed_constraint_fixed_output(&facts, applied.certified().unwrap())
        .unavailable()
        .is_some());
}

#[test]
fn symbolic_component_index_may_alias_a_checked_input_binding() {
    let lifted = fixture(concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(k){component c[2];c[0]=Child();c[1]=Child();",
        "c[0].in<==7;c[k].in<==8;}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[1];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[0], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("component call must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
    assert!(applied.certified().is_some());
    assert!(provider
        .composed_constraint_fixed_output(&facts, applied.certified().unwrap())
        .unavailable()
        .is_some());
}

#[test]
fn competing_child_output_writes_cannot_borrow_the_first_equality() {
    for extra in ["out<==2;", "out<--2;", "out===2;"] {
        let source = format!(
            "template Child(){{signal input in;signal output out;out<==in;{extra}}} \
             template Parent(){{component c=Child();c.in<==7;}}"
        );
        let lifted = fixture(&source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let parent = lifted.hir.definition("Parent").unwrap();
        let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
            panic!("Child must be a template")
        };
        let cfg = build_cfg(&lifted.hir, parent).unwrap();
        let scope = provider.symbolic_root(parent).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
        let output = lifted.hir.template(child).unwrap().ports[1];
        let handle =
            facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
        let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
        else {
            panic!("component call must be reachable")
        };
        let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
        if extra == "out===2;" {
            let applied = applied.certified().expect("equality alone is not a witness write");
            assert!(provider
                .composed_constraint_fixed_output(&facts, applied)
                .unavailable()
                .is_some());
        } else {
            assert!(
                applied.unavailable().unwrap().contains(&SummaryBlocker::UnsupportedContext),
                "repeated child write: {extra}"
            );
        }
    }
}

#[test]
fn repeated_loop_output_effects_cannot_be_counted_as_one_write() {
    let lifted = fixture(concat!(
        "template Child(){signal input in;signal output out;",
        "for(var i=0;i<2;i++){out<==in;}} ",
        "template Parent(){component c=Child();c.in<==7;}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[1];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("component call must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
    assert!(
        applied.unavailable().unwrap().contains(&SummaryBlocker::UnsupportedContext),
        "repeated loop output write"
    );
}

#[test]
fn dynamic_child_loop_has_a_typed_write_blocker() {
    let lifted = fixture(concat!(
        "template Child(){signal input in;signal output out;",
        "for(var i=0;i<17;i++){i=16;out<==in;}} ",
        "template Parent(){component c=Child();c.in<==7;}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let scope = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[1];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("component call must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
    assert!(applied.unavailable().unwrap().iter().any(|blocker| match blocker {
        SummaryBlocker::LocalFacts(reasons) => reasons.iter().any(|reason| {
            let FactBlocker::WitnessWrite(_, WitnessWriteIssue::PossibleRepeat) = reason else {
                return false;
            };
            true
        }),
        _ => false,
    }));
}
