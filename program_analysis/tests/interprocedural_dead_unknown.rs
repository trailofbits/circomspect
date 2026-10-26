// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::interprocedural::{ProjectSummaries, SummaryBlocker};
use circomspect_program_analysis::new_rules::RuleContext;
use parser::hir::lift_project;
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn validated(source: &str, budget: Option<usize>) -> Result<(), SummaryBlocker> {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-dead-unknown-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("Check").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, budget).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    context.validated_definition().map(|_| ())
}

#[test]
fn certified_dead_known_call_does_not_make_definition_incomplete() {
    let source = "function F(){return 7;}function Check(){if(0){var x=F();}return 7;}";
    assert_eq!(validated(source, None), Ok(()));
}

#[test]
fn live_unknown_calls_and_dead_missing_callees_remain_incomplete() {
    for source in [
        "function Check(){var x=Missing();return 7;}",
        "function Check(){if(0){var x=Missing();}return 7;}",
        "template T(){}function Check(){if(0){var x=T();}return 7;}",
    ] {
        assert_eq!(validated(source, None), Err(SummaryBlocker::IncompleteDefinition));
    }
}

#[test]
fn symbolic_guard_and_budget_do_not_turn_provisional_death_into_proof() {
    let symbolic = "function F(){return 7;}function Check(n){if(n){var x=F();}return 7;}";
    assert_eq!(validated(symbolic, None), Err(SummaryBlocker::IncompleteDefinition));
    let bounded = "function F(){return 7;}function Check(){if(0){var x=F();}return 7;}";
    assert_eq!(validated(bounded, Some(0)), Err(SummaryBlocker::IncompleteDefinition));
}

#[test]
fn live_known_call_still_resolves_in_a_complete_definition() {
    let source = "function F(){return 7;}function Check(){var x=F();return 7;}";
    assert_eq!(validated(source, None), Ok(()));
}

#[test]
fn independent_one_live_loop_copy_keeps_unknown_region_blocked() {
    let source = concat!(
        "function F(n){return n;}",
        "function Check(n){for(var i=0;i<2;i++){if(i){var x=F(n);}}return 7;}"
    );
    assert_eq!(validated(source, None), Err(SummaryBlocker::IncompleteDefinition));
}

#[test]
fn independent_dead_source_errors_are_not_discharged() {
    for source in [
        "function Check(){if(0){var x=1+;}return 7;}",
        "function F(n){return n;}function Check(){if(0){var x=F();}return 7;}",
    ] {
        assert_eq!(validated(source, None), Err(SummaryBlocker::IncompleteDefinition));
    }
}
