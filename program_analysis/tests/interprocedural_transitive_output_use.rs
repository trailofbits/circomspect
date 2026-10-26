// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::format_push_string,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ContextEvidence, ProjectOutputStatus, ProjectSummaries,
    SummaryBlocker, SummaryFact,
};
use parser::hir::{lift_project, DefinitionRef, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-transitive-output-use-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let file = directory.join("case.circom");
    fs::write(&file, source).unwrap();
    let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

fn main_evidence(provider: &ProjectSummaries<'_>, project: &LiftedProject) -> ContextEvidence {
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &project.hir)
    else {
        panic!("main must resolve")
    };
    provider.main_evidence(&call).unwrap()
}

fn middle_evidence(provider: &ProjectSummaries<'_>, project: &LiftedProject) -> ContextEvidence {
    let main = main_evidence(provider, project);
    let parent = project.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&project.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &main, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("middle must be reachable")
    };
    provider.call_evidence(&call, &facts, &main).unwrap()
}

fn nested_uses(
    source: &str,
) -> SummaryFact<Vec<circomspect_program_analysis::interprocedural::ProjectOutputUse>> {
    let project = fixture(source);
    assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
    let provider = ProjectSummaries::build(&project, Curve::Bn254).unwrap();
    let main = main_evidence(&provider, &project);
    let definition = project.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &main, None).unwrap();
    provider.closed_project_output_uses(&facts, &main)
}

#[test]
fn nested_component_output_use_keeps_exact_array_elements_separate() {
    let source = concat!(
        "template Leaf(){signal output out[2];out[0]<==1;out[1]<==2;} ",
        "template Middle(){component c=Leaf();signal output y;y<==c.out[0];} ",
        "template Parent(){component m=Middle();} component main=Parent();"
    );
    let uses = nested_uses(source);
    let uses = uses.certified().unwrap();
    let read = uses
        .iter()
        .find(|proof| proof.instance_depth() == 2 && proof.output_indices() == Some(&[0][..]));
    let unused = uses
        .iter()
        .find(|proof| proof.instance_depth() == 2 && proof.output_indices() == Some(&[1][..]));
    assert_eq!(
        read.map(circomspect_program_analysis::interprocedural::ProjectOutputUse::status),
        Some(ProjectOutputStatus::Read)
    );
    assert_eq!(
        unused.map(circomspect_program_analysis::interprocedural::ProjectOutputUse::status),
        Some(ProjectOutputStatus::Unused)
    );
}

#[test]
fn nested_equal_callee_contexts_keep_distinct_component_instances() {
    let source = concat!(
        "template Leaf(){signal output out;out<==1;} ",
        "template Middle(){component c[2];c[0]=Leaf();c[1]=Leaf();",
        "signal output y;y<==c[0].out;} ",
        "template Parent(){component m=Middle();} component main=Parent();"
    );
    let uses = nested_uses(source);
    let uses = uses.certified().unwrap();
    let read = uses
        .iter()
        .find(|proof| proof.instance_depth() == 2 && proof.instance_path()[1].indices() == [0])
        .unwrap();
    let unused = uses
        .iter()
        .find(|proof| proof.instance_depth() == 2 && proof.instance_path()[1].indices() == [1])
        .unwrap();
    assert_eq!(read.status(), ProjectOutputStatus::Read);
    assert_eq!(unused.status(), ProjectOutputStatus::Unused);
    assert_ne!(read.instance_path()[1].site(), unused.instance_path()[1].site());
    assert_ne!(read.source_span(), unused.source_span());
}

#[test]
fn one_loop_call_site_cannot_merge_distinct_array_instances() {
    let source = concat!(
        "template Leaf(){signal output out;out<==1;} ",
        "template Parent(){component c[2];",
        "for(var i=0;i<2;i++){c[i]=Leaf();}} component main=Parent();"
    );
    let project = fixture(source);
    let provider = ProjectSummaries::build(&project, Curve::Bn254).unwrap();
    let main = main_evidence(&provider, &project);
    let definition = project.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &main, None).unwrap();
    let uses = provider.closed_project_output_uses(&facts, &main);
    assert!(uses.certified().is_none());
}

#[test]
fn outputless_failing_sibling_blocks_negative_closure() {
    let source = concat!(
        "template Leaf(){signal output out;out<==1;} ",
        "template Empty(){assert(0);} ",
        "template Middle(){component c=Leaf();component d=Empty();} ",
        "template Parent(){component m=Middle();} component main=Parent();"
    );
    assert!(nested_uses(source).certified().is_none());
}

#[test]
fn outputless_child_with_bound_input_preserves_other_unused_outputs() {
    let source = concat!(
        "template Leaf(){signal output out;out<==1;}",
        "template Empty(){signal input x;x===1;}",
        "template Parent(){component c=Leaf();component e=Empty();e.x<==1;}",
        "component main=Parent();"
    );
    let uses = nested_uses(source);
    let uses = uses.certified().unwrap_or_else(|| panic!("{uses:?}"));
    assert_eq!(uses.len(), 1);
    assert_eq!(uses[0].status(), ProjectOutputStatus::Unused);
    assert_eq!(uses[0].instance_depth(), 1);
}

#[test]
fn nested_outputless_child_inputs_are_checked_before_completing_ancestors() {
    for binding in ["e.x<==1;", ""] {
        let source = format!(
            "template Leaf(){{signal output out;out<==1;}}\
             template Empty(){{signal input x;x===1;}}\
             template Middle(){{component e=Empty();{binding}}}\
             template Parent(){{component c=Leaf();component m=Middle();}}\
             component main=Parent();"
        );
        let uses = nested_uses(&source);
        if binding.is_empty() {
            assert!(uses.unavailable().is_some(), "{uses:?}");
        } else {
            let uses = uses.certified().unwrap_or_else(|| panic!("{uses:?}"));
            assert_eq!(uses.len(), 1);
            assert_eq!(uses[0].status(), ProjectOutputStatus::Unused);
        }
    }
}

#[test]
fn outputless_instances_cannot_borrow_each_others_input_bindings() {
    for bindings in ["e[0].x<==1;e[1].x<==1;", "e[0].x<==1;", "e[1].x<==1;"] {
        let source = format!(
            "template Leaf(){{signal output out;out<==1;}}\
             template Empty(){{signal input x;x===1;}}\
             template Parent(){{component c=Leaf();component e[2];\
             e[0]=Empty();e[1]=Empty();{bindings}}}component main=Parent();"
        );
        let uses = nested_uses(&source);
        assert_eq!(uses.certified().is_some(), bindings.contains(";e[1]"), "{uses:?}");
    }
}

#[test]
fn outputless_child_keeps_missing_duplicate_witness_and_failure_refusals() {
    for (body, parent) in [
        ("x===1;", "component e=Empty();"),
        ("x===1;", "component e=Empty();e.x<==1;e.x<==1;"),
        ("x===1;", "component e=Empty();e.x<--1;"),
        ("x===1;assert(0);", "component e=Empty();e.x<==1;"),
        ("x===1;var bad=1/0;", "component e=Empty();e.x<==1;"),
        ("x===1;", "component e[1];e[0]=Empty();e[1].x<==1;"),
        ("x===1;", "signal input i;component e[1];e[0]=Empty();e[i].x<==1;"),
    ] {
        let source = format!(
            "template Leaf(){{signal output out;out<==1;}}\
             template Empty(){{signal input x;{body}}}\
             template Parent(){{component c=Leaf();{parent}}}component main=Parent();"
        );
        assert!(nested_uses(&source).unavailable().is_some(), "{source}");
    }
}

#[test]
fn incomplete_signal_witnesses_block_root_leaf_and_nested_closure() {
    let valid_leaf = "template Leaf(){signal output out;out<==1;} ";
    let valid_middle = "template Middle(){component c=Leaf();} ";
    let cases = [
        format!(
            "{valid_leaf}{valid_middle}template Parent(){{signal s;component m=Middle();\
             signal output y;y<==s;}}component main=Parent();"
        ),
        concat!(
            "template Leaf(){signal s;signal output out;out<==s;} ",
            "template Middle(){component c=Leaf();} ",
            "template Parent(){component m=Middle();}component main=Parent();"
        )
        .to_string(),
        format!(
            "{valid_leaf}template Middle(){{signal s;component c=Leaf();\
             signal output y;y<==s;}}\
             template Parent(){{component m=Middle();}}component main=Parent();"
        ),
    ];
    for source in cases {
        assert!(nested_uses(&source).certified().is_none(), "{source}");
    }
}

#[test]
fn invalid_generated_equation_and_repeated_writes_block_closure() {
    let bodies = [
        "signal a;signal b;signal c;a<==1;b<==2;c<==3;\
         signal output out;out<==1;a*b+a*c===0;",
        "signal output out;out<==1;out<==2;",
    ];
    for body in bodies {
        let source = format!(
            "template Leaf(){{{body}}}template Middle(){{component c=Leaf();}}\
             template Parent(){{component m=Middle();}}component main=Parent();"
        );
        assert!(nested_uses(&source).certified().is_none(), "{source}");
    }
}

#[test]
fn component_output_read_requires_inputs_before_the_read_site() {
    let prefix = concat!(
        "template Leaf(){signal input in;signal output out;out<==in;} ",
        "template Middle(){component c=Leaf();signal output y;"
    );
    let suffix = "}template Parent(){component m=Middle();}component main=Parent();";
    let early = format!("{prefix}y<==c.out;c.in<==1;{suffix}");
    let ready = format!("{prefix}c.in<==1;y<==c.out;{suffix}");
    assert!(nested_uses(&early).certified().is_none());
    let uses = nested_uses(&ready);
    let uses = uses.certified().unwrap();
    assert!(uses.iter().any(|use_fact| {
        use_fact.instance_depth() == 2 && use_fact.status() == ProjectOutputStatus::Read
    }));
}

#[test]
fn repeated_output_read_cannot_reuse_later_input_readiness_for_an_earlier_site() {
    let source = |bindings| {
        format!(
            "template Leaf(){{signal input in;signal output out;out<==in;}} \
             template Parent(){{component c=Leaf();{bindings}}}component main=Parent();"
        )
    };
    let ready = nested_uses(&source("c.in<==1;var early=c.out+0;var late=c.out+0;"));
    assert!(ready.certified().is_some(), "{ready:?}");
    let unready = nested_uses(&source("var early=c.out+0;c.in<==1;var late=c.out+0;"));
    assert!(unready.certified().is_none(), "{unready:?}");
}

#[test]
fn equal_context_instances_with_one_unready_input_cannot_close_negative_use() {
    let source = concat!(
        "template Leaf(){signal input in;signal output out;out<==in;} ",
        "template Middle(){component c[2];c[0]=Leaf();c[1]=Leaf();",
        "c[0].in<==1;signal output y;y<==c[0].out;} ",
        "template Parent(){component m=Middle();}component main=Parent();"
    );
    assert!(nested_uses(source).certified().is_none());
}

#[test]
fn the_combined_instance_and_output_budget_is_all_or_nothing() {
    let source = |outputs| {
        format!(
            "template Leaf(){{signal output out[{outputs}];}}\
             template Parent(){{component c=Leaf();}}component main=Parent();"
        )
    };
    let complete = fixture(&source(255));
    let provider = ProjectSummaries::build(&complete, Curve::Bn254).unwrap();
    let main = main_evidence(&provider, &complete);
    let definition = complete.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&complete.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &main, None).unwrap();
    let result = provider.closed_project_output_uses(&facts, &main);
    assert_eq!(result.certified().map(Vec::len), Some(255), "{result:?}");

    let over = fixture(&source(256));
    let provider = ProjectSummaries::build(&over, Curve::Bn254).unwrap();
    let main = main_evidence(&provider, &over);
    let definition = over.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&over.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &main, None).unwrap();
    let result = provider.closed_project_output_uses(&facts, &main);
    assert!(result.unavailable().is_some_and(|reasons| {
        reasons
            .contains(&circomspect_program_analysis::interprocedural::SummaryBlocker::ContextBudget)
    }));
}

#[test]
fn outputless_siblings_count_against_the_same_project_budget() {
    let source = |siblings| {
        let mut source = String::from(
            "template Leaf(){signal output out[240];}template Empty(){}template Parent(){\
             component c=Leaf();",
        );
        for index in 0..siblings {
            source.push_str(&format!("component e{index}=Empty();"));
        }
        source.push_str("}component main=Parent();");
        source
    };
    let complete = nested_uses(&source(15));
    assert_eq!(complete.certified().map(Vec::len), Some(240));
    let over = nested_uses(&source(16));
    assert!(over
        .unavailable()
        .is_some_and(|reasons| { reasons.contains(&SummaryBlocker::ContextBudget) }));
}

#[test]
fn symbolic_index_in_nested_caller_prevents_negative_output_use() {
    let source = concat!(
        "template Leaf(){signal output out[2];out[0]<==1;out[1]<==2;} ",
        "template Middle(){signal input i;component c=Leaf();",
        "signal output y;y<==c.out[i];} ",
        "template Parent(){component m=Middle();m.i<==0;} component main=Parent();"
    );
    let result = nested_uses(source);
    assert!(result.certified().is_none());
}

#[test]
fn a_symbolic_library_parent_cannot_claim_nested_unused_output() {
    let project = fixture(concat!(
        "template Leaf(){signal output out;out<==1;} ",
        "template Middle(){component c=Leaf();}"
    ));
    let provider = ProjectSummaries::build(&project, Curve::Bn254).unwrap();
    let definition = project.hir.definition("Middle").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let result = provider.closed_project_output_uses(&facts, &evidence);
    assert!(result.certified().is_none());
}

#[test]
fn foreign_project_facts_and_evidence_cannot_close_an_equal_source_project() {
    let source = concat!(
        "template Leaf(){signal output out;out<==1;} ",
        "template Parent(){component c=Leaf();}component main=Parent();"
    );
    let first = fixture(source);
    let second = fixture(source);
    let first_provider = ProjectSummaries::build(&first, Curve::Bn254).unwrap();
    let second_provider = ProjectSummaries::build(&second, Curve::Bn254).unwrap();
    let main = main_evidence(&first_provider, &first);
    let definition = first.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&first.hir, definition).unwrap();
    let facts = first_provider.analyze_for_evidence(&cfg, &main, None).unwrap();
    let result = second_provider.closed_project_output_uses(&facts, &main);
    assert!(result.unavailable().is_some_and(|reasons| {
        reasons
            .contains(&circomspect_program_analysis::interprocedural::SummaryBlocker::WrongContext)
    }));
}

#[test]
fn a_nested_known_output_read_survives_an_opaque_sibling() {
    let project = fixture(concat!(
        "template Leaf(){signal output out;out<==1;} ",
        "template Middle(){component c=Leaf();signal output y;y<==c.out;",
        "component bad=Missing();} ",
        "template Parent(){component m=Middle();} component main=Parent();"
    ));
    let provider = ProjectSummaries::build(&project, Curve::Bn254).unwrap();
    let middle = middle_evidence(&provider, &project);
    let definition = project.hir.definition("Middle").unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &middle, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("known leaf must be reachable")
    };
    let DefinitionRef::Template(leaf) = call.callee() else { panic!("leaf must be a template") };
    let output = project.hir.template(leaf).unwrap().ports[0];
    let component = project
        .hir
        .components()
        .iter()
        .find(|item| project.hir.symbol(item.symbol).is_some_and(|symbol| symbol.name == "c"))
        .unwrap();
    let handle = facts.component_output_handle(component.id, &[], output, &[]).unwrap();
    let applied = provider.apply_component_output(&facts, &middle, &call, &handle);
    let read = provider.caller_output_read(&facts, applied.certified().unwrap());
    assert!(read.certified().is_some());
    let negative = provider.closed_project_output_uses(&facts, &middle);
    assert!(negative.certified().is_none());
}

#[test]
fn identical_nested_sites_retain_their_distinct_parent_instance_paths() {
    let result = nested_uses(concat!(
        "template Leaf(){signal output out;out<==1;}",
        "template Middle(){component child=Leaf();}",
        "template Parent(){component first=Middle();component second=Middle();}",
        "component main=Parent();"
    ));
    let proofs = result.certified().unwrap();
    assert_eq!(proofs.len(), 2);
    assert!(proofs.iter().all(|proof| proof.status() == ProjectOutputStatus::Unused));
    assert_eq!(proofs[0].instance_depth(), 2);
    assert_eq!(proofs[1].instance_depth(), 2);
    assert_eq!(proofs[0].instance_path()[1].site(), proofs[1].instance_path()[1].site());
    assert_eq!(
        proofs[0].instance_path()[1].callee_evidence().context(),
        proofs[1].instance_path()[1].callee_evidence().context()
    );
    assert_ne!(proofs[0].instance_path()[1], proofs[1].instance_path()[1]);
    assert_ne!(proofs[0].instance_path()[0], proofs[1].instance_path()[0]);
    assert_ne!(proofs[0], proofs[1]);
}

#[test]
fn later_nested_failure_invalidates_previously_collected_negative_output_facts() {
    let source = |flag| {
        format!(
            "template Leaf(){{signal output out;out<==1;}}\
         template Middle(n){{assert(n);component child=Leaf();}}\
         template Parent(){{component first=Middle(1);component second=Middle({flag});}}\
         component main=Parent();"
        )
    };
    let ready = nested_uses(&source(1));
    assert_eq!(ready.certified().map(Vec::len), Some(2), "{ready:?}");
    let invalid = nested_uses(&source(0));
    assert!(invalid.certified().is_none(), "{invalid:?}");
}
