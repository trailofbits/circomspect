use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ProjectOutputStatus, ProjectOutputUse, ProjectSummaries,
    SummaryBlocker, SummaryFact,
};
use parser::hir::{lift_project, DefinitionRef, LiftedProject};
use parser::new_frontend::{load_sources, PortDirection, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-project-output-use-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let file = directory.join("case.circom");
    fs::write(&file, source).unwrap();
    let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

fn internal_use(source: &str, index: usize) -> SummaryFact<ProjectOutputUse> {
    internal_use_at(source, index, &[], None)
}

fn internal_use_at(
    source: &str,
    index: usize,
    output_indices: &[usize],
    budget: Option<usize>,
) -> SummaryFact<ProjectOutputUse> {
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let root = if lifted.hir.mains().is_empty() {
        provider.symbolic_root(parent).unwrap()
    } else {
        let site = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(main) =
            provider.graph().reachable_main_call(site.id(), &lifted.hir)
        else {
            panic!("main must resolve")
        };
        provider.main_evidence(&main).unwrap()
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &root, None).unwrap();
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
    let component = lifted.hir.components()[0].id;
    let handle =
        facts.component_output_handle(component, &[index], output, output_indices).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[index];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("child must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &root, &call, &handle);
    let applied = applied.certified().unwrap_or_else(|| panic!("{:?}", applied.unavailable()));
    if let Some(limit) = budget {
        let pending = provider.analyze_for_evidence(&cfg, &root, Some(limit)).unwrap();
        provider.closed_main_component_output_use(&pending, applied)
    } else {
        provider.closed_main_component_output_use(&facts, applied)
    }
}

#[test]
fn closed_main_distinguishes_read_and_unread_array_instances() {
    let source = concat!(
        "template Child(){signal output out;out<==1;} ",
        "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
        "signal output y;y<==c[0].out;} component main=Parent();"
    );
    let read = internal_use(source, 0);
    let unused = internal_use(source, 1);
    assert_eq!(read.certified().unwrap().status(), ProjectOutputStatus::Read);
    assert_eq!(unused.certified().unwrap().status(), ProjectOutputStatus::Unused);
    assert_eq!(read.certified().unwrap().source_reads().len(), 1);
    assert!(unused.certified().unwrap().source_reads().is_empty());
    assert_ne!(read.certified().unwrap().handle(), unused.certified().unwrap().handle());
}

#[test]
fn parameterized_array_instances_keep_separate_root_use_proofs() {
    let source = concat!(
        "template Child(n){signal output out;out<==1;} ",
        "template Parent(){component c[2];c[0]=Child(0);c[1]=Child(1);",
        "signal output y;y<==c[0].out;} component main=Parent();"
    );
    assert_eq!(internal_use(source, 0).certified().unwrap().status(), ProjectOutputStatus::Read);
    assert_eq!(internal_use(source, 1).certified().unwrap().status(), ProjectOutputStatus::Unused);
}

#[test]
fn a_library_without_main_cannot_certify_an_unused_component_output() {
    let result = internal_use(
        concat!(
            "template Child(){signal output out;out<==1;} ",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();}"
        ),
        1,
    );
    assert!(result.certified().is_none());
}

#[test]
fn opaque_caller_behavior_blocks_a_global_unused_claim() {
    let result = internal_use(
        concat!(
            "template Child(){signal output out;out<==1;} ",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
            "var t=Missing();} component main=Parent();"
        ),
        1,
    );
    assert!(result.certified().is_none());
}

#[test]
fn incomplete_unrelated_definition_blocks_a_project_wide_unused_claim() {
    let result = internal_use(
        concat!(
            "template Child(){signal output out;out<==1;} ",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();} ",
            "template Broken(){Missing();} component main=Parent();"
        ),
        1,
    );
    assert!(result
        .unavailable()
        .is_some_and(|reasons| reasons.contains(&SummaryBlocker::ExternalSummary)));
}

#[test]
fn symbolic_facts_cannot_borrow_a_concrete_main_output_use_proof() {
    let lifted = fixture(concat!(
        "template Child(){signal output out;out<==1;} ",
        "template Parent(n){component c;c=Child();} component main=Parent(0);"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(site.id(), &lifted.hir)
    else {
        panic!("main must resolve")
    };
    let concrete = provider.main_evidence(&main).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let concrete_facts = provider.analyze_for_evidence(&cfg, &concrete, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[0];
    let component = lifted.hir.components()[0].id;
    let handle = concrete_facts.component_output_handle(component, &[], output, &[]).unwrap();
    let call_site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_call(call_site.id(), &concrete_facts)
    else {
        panic!("child must be reachable")
    };
    let applied = provider.apply_component_output(&concrete_facts, &concrete, &call, &handle);
    let applied = applied.certified().unwrap();
    let symbolic = provider.symbolic_root(parent).unwrap();
    let symbolic_facts = provider.analyze_for_evidence(&cfg, &symbolic, None).unwrap();
    let result = provider.closed_main_component_output_use(&symbolic_facts, applied);
    assert!(result
        .unavailable()
        .is_some_and(|reasons| reasons.contains(&SummaryBlocker::WrongContext)));
}

#[test]
fn an_input_bearing_child_needs_a_full_ready_instance_proof() {
    let result = internal_use(
        concat!(
            "template Child(){signal input in;signal output out;out<==in;} ",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
            "c[0].in<==1;c[1].in<==2;} component main=Parent();"
        ),
        1,
    );
    assert!(result.certified().is_none());
}

#[test]
fn a_child_internal_read_prevents_an_unused_output_claim() {
    let result = internal_use(
        concat!(
            "template Child(){signal output out;out<==1;signal t;t<==out+1;} ",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();}",
            "component main=Parent();"
        ),
        1,
    );
    assert_eq!(result.certified().map(ProjectOutputUse::status), Some(ProjectOutputStatus::Read));
}

#[test]
fn a_different_child_output_element_does_not_count_as_the_queried_read() {
    let source = concat!(
        "template Child(){signal output out[2];out[0]<==1;out[1]<==2;",
        "signal t;t<==out[0];} ",
        "template Parent(){component c[2];c[0]=Child();c[1]=Child();}",
        "component main=Parent();"
    );
    let result = internal_use_at(source, 1, &[1], None);
    assert_eq!(result.certified().map(ProjectOutputUse::status), Some(ProjectOutputStatus::Unused));
}

#[test]
fn a_symbolic_child_output_index_blocks_an_unused_claim() {
    let source = concat!(
        "template Child(){signal output out[2];out[0]<==1;out[1]<==2;",
        "var i=0;signal t;t<==out[i];} ",
        "template Parent(){component c[2];c[0]=Child();c[1]=Child();}",
        "component main=Parent();"
    );
    let result = internal_use_at(source, 1, &[1], None);
    assert!(result.certified().is_none());
}

#[test]
fn a_child_output_equality_is_an_actual_read() {
    let source = concat!(
        "template Child(){signal output out;out<==1;out===1;} ",
        "template Parent(){component c[2];c[0]=Child();c[1]=Child();}",
        "component main=Parent();"
    );
    let result = internal_use(source, 1);
    assert_eq!(result.certified().map(ProjectOutputUse::status), Some(ProjectOutputStatus::Read));
}

#[test]
fn child_branch_coverage_must_be_proved_before_an_unused_claim() {
    let result = internal_use(
        concat!(
            "template Child(){signal output out;if(1){out<==1;}else{out<==2;}} ",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();}",
            "component main=Parent();"
        ),
        1,
    );
    assert!(result.certified().is_none());
}

#[test]
fn an_exhausted_local_budget_cannot_prove_an_unused_output() {
    let source = concat!(
        "template Child(){signal output out;out<==1;} ",
        "template Parent(){component c[2];c[0]=Child();c[1]=Child();}",
        "component main=Parent();"
    );
    let result = internal_use_at(source, 1, &[], Some(0));
    assert!(result.certified().is_none());
}

#[test]
fn an_exported_main_output_is_an_environment_read() {
    let lifted = fixture("template Parent(){signal output y;} component main=Parent();");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(template) = parent else { panic!("Parent must be a template") };
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(site.id(), &lifted.hir)
    else {
        panic!("main must resolve")
    };
    let root = provider.main_evidence(&main).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &root, None).unwrap();
    let port = lifted.hir.template(template).unwrap().ports[0];
    let handle = facts.port_handle(port, &[]).unwrap();
    let result = provider.exported_main_output_use(&facts, &root, &handle);
    assert_eq!(result.certified().unwrap().status(), ProjectOutputStatus::Read);
}

#[test]
fn a_main_input_cannot_be_mislabeled_as_an_exported_output() {
    let lifted = fixture("template Parent(){signal input x;} component main=Parent();");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(template) = parent else { panic!("Parent must be a template") };
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(site.id(), &lifted.hir)
    else {
        panic!("main must resolve")
    };
    let root = provider.main_evidence(&main).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &root, None).unwrap();
    let port = lifted.hir.template(template).unwrap().ports[0];
    let handle = facts.port_handle(port, &[]).unwrap();
    assert!(provider.exported_main_output_use(&facts, &root, &handle).certified().is_none());
}

#[test]
fn an_exact_exported_main_output_array_element_is_environment_read() {
    let lifted = fixture("template Parent(){signal output y[2];} component main=Parent();");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(template) = parent else { panic!("Parent must be a template") };
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(site.id(), &lifted.hir)
    else {
        panic!("main must resolve")
    };
    let root = provider.main_evidence(&main).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &root, None).unwrap();
    let port = lifted.hir.template(template).unwrap().ports[0];
    let handle = facts.port_handle(port, &[1]).unwrap();
    let result = provider.exported_main_output_use(&facts, &root, &handle);
    assert_eq!(result.certified().unwrap().status(), ProjectOutputStatus::Read);
}
