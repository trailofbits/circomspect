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
    CallOwner, CallReachability, EnumeratedComponentOutput, ProjectOutputStatus, ProjectSummaries,
    SummaryBlocker, SummaryFact,
};
use circomspect_program_analysis::new_rules::RuleContext;
use parser::hir::{lift_project, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-output-enumeration-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

fn enumerated(source: &str) -> SummaryFact<Vec<EnumeratedComponentOutput>> {
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let root = if lifted.hir.mains().is_empty() {
        provider.symbolic_root(parent).unwrap()
    } else {
        let site = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(main) =
            provider.graph().reachable_main_call(site.id(), provider.hir())
        else {
            panic!("main must be reachable")
        };
        provider.main_evidence(&main).unwrap()
    };
    let cfg = build_cfg(provider.hir(), parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &root, None).unwrap();
    RuleContext::new(&facts, &provider, &root).unwrap().exact_component_outputs()
}

#[test]
fn scalar_output_candidates_keep_distinct_checked_ports_and_source_sites() {
    let source = concat!(
        "template Child(){signal output a;signal output b;a<==1;b<==2;} ",
        "template Parent(){component c=Child();signal output y;y<==c.a;} ",
        "component main=Parent();"
    );
    let result = enumerated(source);
    let outputs = result.certified().unwrap();
    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0].source_span(), outputs[1].source_span());
    assert_eq!(outputs[0].source_span().start(), source.rfind("Child()").unwrap());
    assert_ne!(outputs[0].applied_port().handle(), outputs[1].applied_port().handle());
}

#[test]
fn component_and_port_arrays_enumerate_every_exact_element() {
    let source = concat!(
        "template Child(){signal output out[2];out[0]<==1;out[1]<==2;} ",
        "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
        "signal output y;y<==c[0].out[0];} component main=Parent();"
    );
    let result = enumerated(source);
    let outputs = result.certified().unwrap();
    assert_eq!(outputs.len(), 4);
    let sites: std::collections::BTreeSet<_> =
        outputs.iter().map(EnumeratedComponentOutput::site).collect();
    assert_eq!(sites.len(), 2);
    for left in 0..outputs.len() {
        for right in left + 1..outputs.len() {
            assert_ne!(
                outputs[left].applied_port().handle(),
                outputs[right].applied_port().handle()
            );
        }
    }
}

#[test]
fn opaque_sibling_blocks_complete_enumeration_instead_of_hiding_outputs() {
    let source = concat!(
        "template Child(){signal output out;out<==1;} ",
        "template Parent(){component a=Child();component b=Missing();} ",
        "component main=Parent();"
    );
    let result = enumerated(source);
    assert!(result.certified().is_none(), "{result:?}");
}

#[test]
fn total_handle_cap_is_enforced_across_small_component_arrays() {
    let mut source = String::from("template Child(){signal output out[16];} template Parent(){");
    for index in 0..9 {
        source.push_str(&format!("component c{index}[2];c{index}[0]=Child();c{index}[1]=Child();"));
    }
    source.push_str("} component main=Parent();");
    let result = enumerated(&source);
    assert_eq!(
        result.unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::ContextBudget]))
    );
}

#[test]
fn exactly_256_handles_form_a_complete_certificate() {
    let mut source = String::from("template Child(){signal output out[16];} template Parent(){");
    for index in 0..16 {
        source.push_str(&format!("component c{index}=Child();"));
    }
    source.push_str("} component main=Parent();");
    let result = enumerated(&source);
    assert_eq!(result.certified().map(Vec::len), Some(256), "{result:?}");
}

#[test]
fn duplicate_instantiation_never_yields_a_partial_certificate() {
    let source = concat!(
        "template Child(){signal output out;out<==1;} ",
        "template Parent(){component c;c=Child();c=Child();} ",
        "component main=Parent();"
    );
    let result = enumerated(source);
    assert!(result.certified().is_none(), "{result:?}");
}

#[test]
fn unbound_child_input_enumerates_a_candidate_but_cannot_prove_project_unused() {
    let source = concat!(
        "template Child(){signal input x;signal output out;out<==x;} ",
        "template Parent(){component c=Child();} component main=Parent();"
    );
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(site.id(), provider.hir())
    else {
        panic!("main must be reachable")
    };
    let root = provider.main_evidence(&main).unwrap();
    let cfg = build_cfg(provider.hir(), parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &root, None).unwrap();
    let outputs = provider.exact_component_outputs(&facts, &root);
    let outputs = outputs.certified().unwrap();
    assert_eq!(outputs.len(), 1);
    let use_fact = provider.closed_project_output_uses(&facts, &root);
    assert!(use_fact.certified().is_none());
}

#[test]
fn symbolic_child_output_shape_cannot_produce_a_partial_list() {
    let source = concat!(
        "template Child(n){signal output out[n];} ",
        "template Parent(m){component c=Child(m);}"
    );
    let result = enumerated(source);
    assert!(result.certified().is_none(), "{result:?}");
}

#[test]
fn enumerated_outputs_retain_closed_project_use_provenance() {
    let source = concat!(
        "template Child(){signal output a;signal output b;a<==1;b<==2;} ",
        "template Parent(){component c=Child();signal output y;y<==c.a;} ",
        "component main=Parent();"
    );
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(site.id(), provider.hir())
    else {
        panic!("main must be reachable")
    };
    let root = provider.main_evidence(&main).unwrap();
    let cfg = build_cfg(provider.hir(), parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &root, None).unwrap();
    let result = provider.exact_component_outputs(&facts, &root);
    let outputs = result.certified().unwrap();
    let project_uses = provider.closed_project_output_uses(&facts, &root);
    let project_uses = project_uses.certified().unwrap();
    let mut statuses = Vec::new();
    for output in outputs {
        let use_fact = project_uses
            .iter()
            .find(|proof| proof.handle() == output.applied_port().handle())
            .unwrap();
        statuses.push(use_fact.status());
    }
    assert_eq!(statuses, [ProjectOutputStatus::Read, ProjectOutputStatus::Unused]);
}

#[test]
fn empty_outputs_do_not_require_selected_instance_uniqueness() {
    for outputs in ["", "signal output empty[0];"] {
        let source = format!(
            "template Child(){{{outputs}}}template Parent(){{component c;c=Child();c=Child();}}\
             component main=Parent();"
        );
        let result = enumerated(&source);
        assert_eq!(result.certified(), Some(&Vec::new()), "{outputs}: {result:?}");
    }
}

#[test]
fn late_invalid_output_dimensions_precede_selected_instance_conflicts() {
    let result = enumerated(concat!(
        "template Child(n){signal output first;signal output late[n-2];first<==1;}",
        "template Parent(){component c;c=Child(1);c=Child(1);}component main=Parent();"
    ));
    assert_eq!(
        result.unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::UnsupportedContext,]))
    );
}
