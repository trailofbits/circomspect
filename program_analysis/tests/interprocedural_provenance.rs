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

#[path = "support/projects.rs"]
mod projects;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ProjectAnalysis, SummaryBlocker,
};
use circomspect_program_analysis::rules::{RuleContext, RuleContextError};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> parser::hir::LiftedProject {
    projects::lift_source(source, "circomspect-provenance")
}

#[test]
fn main_and_child_paths_have_exact_source_order_and_symbolic_roots_are_empty() {
    let lifted = fixture(
        "template Leaf(n){var x=n;} template Parent(n){component c=Leaf(n);}\
         component main=Parent(7);",
    );
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let leaf = lifted.hir.definition("Leaf").unwrap();
    let root_evidence = provider.contexts().symbolic_root(leaf).unwrap();
    let leaf_cfg = build_cfg(&lifted.hir, leaf).unwrap();
    let root_facts =
        provider.contexts().analyze_for_evidence(&leaf_cfg, &root_evidence, None).unwrap();
    let root = RuleContext::new(&root_facts, &provider, &root_evidence).unwrap();
    assert!(root.call_path().is_empty());
    assert!(root.incoming_call_site().is_none());

    let main_site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main_call) =
        provider.graph().reachable_main_call(main_site.id(), &lifted.hir)
    else {
        panic!("reachable main")
    };
    let main_evidence = provider.contexts().main_evidence(&main_call).unwrap();
    let parent_cfg = build_cfg(&lifted.hir, parent).unwrap();
    let parent_facts =
        provider.contexts().analyze_for_evidence(&parent_cfg, &main_evidence, None).unwrap();
    let parent_context = RuleContext::new(&parent_facts, &provider, &main_evidence).unwrap();
    assert_eq!(parent_context.call_path().len(), 1);
    assert_eq!(parent_context.incoming_call_site().unwrap().span(), main_site.span);

    let child_site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(child_call) =
        provider.graph().reachable_call(child_site.id(), &parent_facts)
    else {
        panic!("reachable child")
    };
    let child_evidence =
        provider.contexts().call_evidence(&child_call, &parent_facts, &main_evidence).unwrap();
    let child_facts =
        provider.contexts().analyze_for_evidence(&leaf_cfg, &child_evidence, None).unwrap();
    let child = RuleContext::new(&child_facts, &provider, &child_evidence).unwrap();
    let path = child.call_path();
    assert_eq!(path.len(), 2);
    assert_eq!(path[0].span(), main_site.span);
    assert_eq!(path[1].span(), child_site.span);
    assert_eq!(child.incoming_call_site().unwrap().span(), child_site.span);
    assert_eq!(path[0].callee(), parent);
    assert_eq!(path[1].callee(), leaf);
}

#[test]
fn equal_callee_arguments_do_not_exchange_caller_provenance() {
    let lifted = fixture(
        "template Leaf(n){var x=n;} template Left(){component c=Leaf(7);}\
         template Right(){component c=Leaf(7);}",
    );
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let leaf = lifted.hir.definition("Leaf").unwrap();
    let leaf_cfg = build_cfg(&lifted.hir, leaf).unwrap();
    let mut evidence = Vec::new();
    for name in ["Left", "Right"] {
        let parent = lifted.hir.definition(name).unwrap();
        let parent_evidence = provider.contexts().symbolic_root(parent).unwrap();
        let parent_cfg = build_cfg(&lifted.hir, parent).unwrap();
        let parent_facts =
            provider.contexts().analyze_for_evidence(&parent_cfg, &parent_evidence, None).unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
        let CallReachability::Reachable(call) =
            provider.graph().reachable_call(site.id(), &parent_facts)
        else {
            panic!("reachable child")
        };
        evidence.push(
            provider.contexts().call_evidence(&call, &parent_facts, &parent_evidence).unwrap(),
        );
    }
    assert_eq!(evidence[0].context(), evidence[1].context());
    let first = provider.contexts().analyze_for_evidence(&leaf_cfg, &evidence[0], None).unwrap();
    let second = provider.contexts().analyze_for_evidence(&leaf_cfg, &evidence[1], None).unwrap();
    let first_context = RuleContext::new(&first, &provider, &evidence[0]).unwrap();
    let second_context = RuleContext::new(&second, &provider, &evidence[1]).unwrap();
    assert_ne!(first_context.call_path(), second_context.call_path());
    assert_eq!(
        RuleContext::new(&first, &provider, &evidence[1]).err(),
        Some(RuleContextError::MismatchedFacts(SummaryBlocker::WrongContext))
    );
}
