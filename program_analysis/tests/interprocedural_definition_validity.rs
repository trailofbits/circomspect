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
use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::interprocedural::{ProjectSummaries, SummaryBlocker};
use circomspect_program_analysis::new_rules::RuleContext;
use parser::hir::{lift_project, DefinitionRef, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-definition-validity-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

fn with_scope(source: &str, test: impl FnOnce(&RuleContext<'_, '_, '_>)) {
    let lifted = fixture(source);
    let definition = lifted.hir.definition("Check").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    test(&context);
}

#[test]
fn validated_header_counts_only_function_or_template_parameters() {
    for (source, count) in [
        ("function Check(a,b,c,d,e,f,g,h){return 0;}", 8),
        ("template Check(a,b,c,d,e,f,g){signal input x;}", 7),
    ] {
        with_scope(source, |context| {
            let header = context.validated_header().unwrap();
            assert_eq!(header.definition(), context.call_context().definition());
            assert_eq!(header.name(), "Check");
            assert_eq!(header.parameter_count(), count);
            assert_eq!(header.name_span().start(), source.find("Check").unwrap());
            assert!(context.validated_definition().is_ok());
        });
    }
}

#[test]
fn malformed_header_cannot_supply_parameter_count_or_complete_definition() {
    with_scope("function Check(a,b,c,d,e,f,g,g){return 0;}", |context| {
        assert_eq!(context.validated_header().err(), Some(SummaryBlocker::IncompleteDefinition));
        assert_eq!(
            context.validated_definition().err(),
            Some(SummaryBlocker::IncompleteDefinition)
        );
    });
}

#[test]
fn incomplete_body_preserves_valid_header_but_blocks_complete_cfg() {
    with_scope("function Check(a,b,c,d,e,f,g,h){var x=Missing();return 0;}", |context| {
        assert_eq!(context.validated_header().unwrap().parameter_count(), 8);
        assert_eq!(
            context.validated_definition().err(),
            Some(SummaryBlocker::IncompleteDefinition)
        );
    });
}

#[test]
fn complete_call_result_discharge_is_limited_to_checked_source_sites() {
    with_scope(
        "function F(){return 7;} template Check(){var x=F();signal output out;out<==x;}",
        |context| assert!(context.validated_definition().is_ok()),
    );
    with_scope(
        "function F(){return 7;} template Check(){var x=Missing();signal output out;out<==x;}",
        |context| {
            assert_eq!(
                context.validated_definition().err(),
                Some(SummaryBlocker::IncompleteDefinition)
            );
        },
    );
}

#[test]
fn nonconstant_call_result_paths_cannot_discharge_incomplete_shape() {
    with_scope(
        "function F(){return 7;} template Check(n){var x=F();if(n){x=8;}signal output out;out<==x;}",
        |context| {
            assert_eq!(
                context.validated_definition().err(),
                Some(SummaryBlocker::IncompleteDefinition)
            );
        },
    );
}

#[test]
fn budget_limited_call_result_cannot_validate_a_partial_definition() {
    let lifted =
        fixture("function F(){return 7;} template Check(){var x=F();signal output out;out<==x;}");
    let definition = lifted.hir.definition("Check").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, Some(1)).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    assert_eq!(context.validated_definition().err(), Some(SummaryBlocker::IncompleteDefinition));
}

#[test]
fn another_definition_error_does_not_invalidate_this_header_or_body() {
    let source = "function Broken(){var x=Missing();return 0;} function Check(){return 7;}";
    with_scope(source, |context| {
        assert!(context.validated_header().is_ok());
        assert!(context.validated_definition().is_ok());
    });
}

#[test]
fn incomplete_included_library_does_not_invalidate_a_clean_definition() {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-definition-included-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    fs::write(directory.join("lib.circom"), "function Broken(){return Missing();}").unwrap();
    let root = directory.join("root.circom");
    fs::write(&root, "include \"lib.circom\"; function Check(){return 7;}").unwrap();
    let loaded = load_sources(&[root], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(!lifted.incomplete.is_empty());
    let definition = lifted.hir.definition("Check").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    assert!(context.validated_header().is_ok());
    assert!(context.validated_definition().is_ok());
}

#[test]
fn bus_definition_cannot_be_mistaken_for_a_function_or_template_header() {
    with_scope("bus Check(){signal input x;}", |context| {
        assert_eq!(context.call_context().definition(), context.facts().definition());
        let DefinitionRef::Bus(_) = context.call_context().definition() else { panic!("bus") };
        assert_eq!(context.validated_header().err(), Some(SummaryBlocker::UnsupportedContext));
    });
}

#[test]
fn malformed_parameter_syntax_cannot_leave_a_validated_partial_header() {
    for source in [
        "function Check(a,b,c,d,e,f,g h){return 0;}",
        "function Check(a,b,c,d,e,f,g,h,){return 0;}",
        "function Check(a,b,c,d,e,f,g,,h){return 0;}",
    ] {
        let lifted = fixture(source);
        assert!(!lifted.syntax_diagnostics.is_empty());
        assert!(lifted.hir.definition("Check").is_none());
    }
}
