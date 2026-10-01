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
    internal_use_at_option(source, index, output_indices, budget)
        .unwrap_or_else(|| panic!("the selected component output must be applicable"))
}

fn internal_use_at_option(
    source: &str,
    index: usize,
    output_indices: &[usize],
    budget: Option<usize>,
) -> Option<SummaryFact<ProjectOutputUse>> {
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
    let component = lifted
        .hir
        .components()
        .iter()
        .find(|item| lifted.hir.symbol(item.symbol).is_some_and(|symbol| symbol.name == "c"))
        .unwrap();
    let symbol = lifted.hir.symbol(component.symbol).unwrap();
    let indices = if symbol.rank == 0 { Vec::new() } else { vec![index] };
    let handle = facts.component_output_handle(component.id, &indices, output, output_indices);
    let handle = handle.unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[index];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("child must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &root, &call, &handle);
    let applied = applied.certified()?;
    if let Some(limit) = budget {
        let pending = provider.analyze_for_evidence(&cfg, &root, Some(limit)).unwrap();
        Some(provider.closed_main_component_output_use(&pending, applied))
    } else {
        Some(provider.closed_main_component_output_use(&facts, applied))
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
fn fully_bound_scalar_child_outputs_have_closed_project_use() {
    let unused = internal_use(
        concat!(
            "template Child(){signal input in;signal output out;out<==in;} ",
            "template Parent(){component c=Child();",
            "c.in<==2;} component main=Parent();"
        ),
        0,
    );
    assert_eq!(unused.certified().map(ProjectOutputUse::status), Some(ProjectOutputStatus::Unused));
    let read = internal_use(
        concat!(
            "template Child(){signal input in;signal output out;out<==in;} ",
            "template Parent(){component c=Child();",
            "c.in<==2;signal output y;y<==c.out;} ",
            "component main=Parent();"
        ),
        0,
    );
    assert_eq!(read.certified().map(ProjectOutputUse::status), Some(ProjectOutputStatus::Read));
    assert_eq!(read.certified().map(|proof| proof.source_reads().len()), Some(1));
}

#[test]
fn missing_or_partial_scalar_input_cannot_prove_output_use() {
    for child_and_bindings in
        [("signal input in;", ""), ("signal input a;signal input b;", "c.a<==1;")]
    {
        let (ports, bindings) = child_and_bindings;
        let source = format!(
            "template Child(){{{ports}signal output out;out<==1;}} \
             template Parent(){{component c=Child();{bindings}}} \
             component main=Parent();"
        );
        assert!(internal_use(&source, 0)
            .unavailable()
            .is_some_and(|reasons| reasons.contains(&SummaryBlocker::MissingInputBinding)));
    }
}

#[test]
fn competing_input_writes_and_early_output_reads_abstain() {
    for body in [
        "if(1<<1){c.in<==1;}else{c.in<==2;}",
        "c.in<==1;c.in<==1;",
        "var t=Missing();c.in<==1;",
        "signal output y;y<==c.out;c.in<==1;",
    ] {
        let source = format!(
            "template Child(){{signal input in;signal output out;out<==in;}} \
             template Parent(){{component c=Child();{body}}} \
             component main=Parent();"
        );
        assert!(internal_use(&source, 0).certified().is_none());
    }
}

#[test]
fn symbolic_or_aggregate_child_inputs_cannot_close_an_unused_claim() {
    let symbolic = concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(k){component c[2];c[0]=Child();c[1]=Child();",
        "c[0].in<==2;c[k].in<==3;} component main=Parent(0);"
    );
    let lifted = fixture(symbolic);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    assert!(internal_use(symbolic, 0).certified().is_none());
    let array = concat!(
        "template Child(){signal input in[2];signal output out;out<==in[0];} ",
        "template Parent(){component c=Child();",
        "c.in[0]<==1;c.in[1]<==2;} component main=Parent();"
    );
    assert!(internal_use(array, 0)
        .unavailable()
        .is_some_and(|reasons| reasons.contains(&SummaryBlocker::UnsupportedContext)));
    let bus = concat!(
        "bus B(){signal x;} ",
        "template Child(){B input in;signal output out;out<==in.x;} ",
        "template Parent(){component c=Child();",
        "c.in.x<==1;} component main=Parent();"
    );
    assert!(internal_use(bus, 0)
        .unavailable()
        .is_some_and(|reasons| reasons.contains(&SummaryBlocker::UnsupportedContext)));
}

#[test]
fn incomplete_project_blocks_a_bound_child_unused_claim() {
    let source = concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(){component c=Child();c.in<==1;} ",
        "template Broken(){Missing();} component main=Parent();"
    );
    assert!(internal_use(source, 0)
        .unavailable()
        .is_some_and(|reasons| reasons.contains(&SummaryBlocker::ExternalSummary)));
}

#[test]
fn an_exhausted_scalar_input_analysis_cannot_claim_unused() {
    let source = concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(){component c=Child();c.in<==1;} component main=Parent();"
    );
    assert!(internal_use_at(source, 0, &[], Some(0)).certified().is_none());
}

#[test]
fn unproved_sibling_inputs_block_project_wide_unused_claims() {
    for bindings in ["c[1].in<==2;", "c[0].in<==1;c[1].in<==2;"] {
        let same_child = format!(
            "template Child(){{signal input in;signal output out;out<==in;}} \
             template Parent(){{component c[2];c[0]=Child();c[1]=Child();{bindings}}} \
             component main=Parent();"
        );
        assert!(internal_use(&same_child, 1)
            .unavailable()
            .is_some_and(|reasons| reasons.contains(&SummaryBlocker::UnsupportedContext)));
    }
    let other_child = concat!(
        "template Child(){signal output out;out<==1;} ",
        "template Needs(){signal input in;signal output out;out<==in;} ",
        "template Parent(){component c[1];c[0]=Child();component d=Needs();} ",
        "component main=Parent();"
    );
    assert!(internal_use(other_child, 0)
        .unavailable()
        .is_some_and(|reasons| reasons.contains(&SummaryBlocker::UnsupportedContext)));
    let nested_sibling = concat!(
        "template Child(){signal output out;out<==1;} ",
        "template Needs(){signal input in;signal output out;out<==in;} ",
        "template Wrapper(){signal output out;out<==1;component d=Needs();} ",
        "template Parent(){component c[1];c[0]=Child();component w=Wrapper();} ",
        "component main=Parent();"
    );
    assert!(internal_use(nested_sibling, 0).certified().is_none());
}

#[test]
fn an_uninstantiated_component_array_element_blocks_the_input_bearing_claim() {
    let source = concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(){component c[2];c[0]=Child();c[0].in<==1;} ",
        "component main=Parent();"
    );
    assert!(internal_use(source, 0).certified().is_none());
}

#[test]
fn an_uninstantiated_no_input_array_element_blocks_project_unused() {
    let source = concat!(
        "template Child(){signal output out;out<==1;} ",
        "template Parent(){component c[2];c[0]=Child();} ",
        "component main=Parent();"
    );
    assert!(internal_use(source, 0).certified().is_none());
}

#[test]
fn a_reachable_assertion_failure_blocks_project_unused() {
    let source = concat!(
        "function Fail(){assert(0);return 1;} ",
        "template Child(){signal output out;out<==1;} ",
        "template Parent(){component c=Child();var t=Fail();} ",
        "component main=Parent();"
    );
    assert!(internal_use(source, 0).certified().is_none());
}

#[test]
fn parent_assertions_require_a_proven_true_condition() {
    for (condition, expected) in [("0", None), ("1", Some(ProjectOutputStatus::Unused))] {
        let source = format!(
            "template Child(){{signal output out;out<==1;}} \
             template Parent(){{component c=Child();assert({condition});}} \
             component main=Parent();"
        );
        let result = internal_use(&source, 0);
        assert_eq!(
            result.certified().map(ProjectOutputUse::status),
            expected,
            "{:?}",
            result.unavailable()
        );
    }
}

#[test]
fn unproved_parameter_assertions_abstain_for_concrete_main_contexts() {
    for argument in [0, 1] {
        let source = format!(
            "template Child(){{signal output out;out<==1;}} \
             template Parent(n){{component c=Child();assert(n);}} \
             component main=Parent({argument});"
        );
        let lifted = fixture(&source);
        assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
        assert!(!lifted.incomplete.is_empty());
        let result = internal_use(&source, 0);
        assert!(result
            .unavailable()
            .is_some_and(|reasons| reasons.contains(&SummaryBlocker::ExternalSummary)));
    }
}

#[test]
fn parent_and_child_traps_block_project_unused() {
    for trap in ["assert(0);", "var t=1/0;", "var x[1]=[1];var t=x[1];", "var x[1]=[1];x[1]=2;"] {
        let parent = format!(
            "template Child(){{signal output out;out<==1;}} \
             template Parent(){{component c=Child();{trap}}} component main=Parent();"
        );
        assert!(internal_use(&parent, 0).certified().is_none(), "parent trap {trap}");
        let child = format!(
            "template Child(){{{trap}signal output out;out<==1;}} \
             template Parent(){{component c=Child();}} component main=Parent();"
        );
        assert!(internal_use(&child, 0).certified().is_none(), "child trap {trap}");
    }
}

#[test]
fn compound_division_cannot_support_a_project_unused_certificate() {
    for trap in ["var x=1;x/=0;", "var x=1;x%=0;"] {
        let source = format!(
            "template Child(){{signal output out;out<==1;}} \
             template Parent(){{component c=Child();{trap}}} component main=Parent();"
        );
        let result = internal_use_at_option(&source, 0, &[], None);
        assert!(result.as_ref().map_or(true, |fact| fact.certified().is_none()));
    }
}

#[test]
fn a_failing_direct_sibling_template_blocks_project_unused() {
    let source = concat!(
        "template Child(){signal output out;out<==1;} ",
        "template Sibling(){signal output out;assert(0);out<==1;} ",
        "template Parent(){component c=Child();component d=Sibling();} ",
        "component main=Parent();"
    );
    assert!(internal_use(source, 0).certified().is_none());
    let safe = source.replace("assert(0)", "assert(1)");
    assert_eq!(
        internal_use(&safe, 0).certified().map(ProjectOutputUse::status),
        Some(ProjectOutputStatus::Unused)
    );
}

#[test]
fn an_indirect_child_of_main_cannot_borrow_the_direct_main_claim() {
    let lifted = fixture(concat!(
        "template Child(){signal input in;signal output out;out<==in;} ",
        "template Parent(){component c=Child();c.in<==1;} ",
        "template Grand(){component p=Parent();} component main=Grand();"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("Child must be a template")
    };
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let root = provider.symbolic_root(parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &root, None).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[1];
    let handle =
        facts.component_output_handle(lifted.hir.components()[0].id, &[], output, &[]).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("child must be reachable")
    };
    let applied = provider.apply_component_output(&facts, &root, &call, &handle);
    let applied = applied.certified().unwrap();
    assert!(provider.closed_main_component_output_use(&facts, applied).certified().is_none());
}

#[test]
fn a_nested_child_component_keeps_project_use_unavailable() {
    let source = concat!(
        "template Nested(){signal input in;signal output out;out<==in;} ",
        "template Child(){signal input in;signal output out;out<==in;",
        "component d=Nested();} ",
        "template Parent(){component c=Child();c.in<==1;} ",
        "component main=Parent();"
    );
    assert!(internal_use(source, 0).certified().is_none());
}

#[test]
fn an_anonymous_sibling_cannot_complete_the_direct_child_project_scope() {
    let source = concat!(
        "template Child(){signal output out;out<==1;} ",
        "template Nested(){signal input in;signal output out;out<==in;} ",
        "template Parent(){component c[1];c[0]=Child();",
        "signal output y;y<==c[0].out;signal output z;z<==Nested()(in<==1);} ",
        "component main=Parent();"
    );
    let lifted = fixture(source);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    assert!(internal_use(source, 0).certified().is_none());
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
