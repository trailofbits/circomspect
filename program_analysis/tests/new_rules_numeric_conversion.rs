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
mod support;

use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::interprocedural::ProjectSummaries;
use circomspect_program_analysis::new_rules::{numeric, RuleContext, RuleKind, RuleResult, SourceMap};
use parser::hir::lift_project;
use parser::new_frontend::{load_sources, LoadedProject, Version, VersionPolicy};
use program_structure::report::MessageCategory;
use program_structure::utils::constants::Curve;
use serde_json::Value;

fn conversion(width: usize, extra: &str) -> String {
    format!(
        "template Decompose(){{signal input value;signal output digits[{width}];var sum=0;\
         for(var i=0;i<{width};i++){{digits[i]<--0;digits[i]*(digits[i]-1)===0;\
         sum+=digits[i]*(2**i);}}sum===value;{extra}}}"
    )
}

fn inspect(source: &str, curve: Curve) -> (LoadedProject, RuleResult) {
    inspect_with_budget(source, curve, None)
}

fn inspect_with_budget(
    source: &str,
    curve: Curve,
    budget: Option<usize>,
) -> (LoadedProject, RuleResult) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-conversion-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    let definition = lifted.hir.definition("Decompose").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let provider = ProjectSummaries::build(&lifted, curve).unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, budget).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    let rule = numeric::rules()
        .iter()
        .find(|rule| rule.kind() == RuleKind::NonstrictBinaryConversion)
        .unwrap();
    (loaded, rule.run(&context))
}

#[test]
fn complete_library_conversion_reports_checked_pair_and_renders_cs0010() {
    let source = conversion(64, "");
    let (loaded, result) = inspect(&source, Curve::Goldilocks);
    let findings: Vec<_> = result
        .findings()
        .iter()
        .filter(|finding| finding.kind() == RuleKind::NonstrictBinaryConversion)
        .cloned()
        .collect();
    assert_eq!(findings.len(), 1, "conversion findings: {}", findings.len());
    let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
    let report = findings[0].to_report(&sources).unwrap();
    assert_eq!(report.id(), "CS0010");
    assert_eq!(*report.category(), MessageCategory::Warning);
    assert!(report.message().contains("same field input"));
    assert!(report.message().contains("distinct 64-bit vectors"));
    assert!(report.message().contains("Goldilocks"));
    let start = source.find("digits[64]").unwrap();
    assert_eq!(report.primary()[0].range.start, start);
    let output = loaded.files[0].path.with_extension("sarif.json");
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Warning, &[], &output).unwrap(),
        (1, 1)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
    let item = &sarif["runs"][0]["results"][0];
    assert_eq!(item["ruleId"], "CS0010");
    assert_eq!(item["level"], "warning");
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Error, &[], &output).unwrap(),
        (0, 0)
    );
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Warning, &["CS0010"], &output)
            .unwrap(),
        (0, 0)
    );
    let hidden = SourceMap::from_loaded(&loaded, &[]).unwrap();
    assert_eq!(
        support::render(&findings, &hidden, MessageCategory::Warning, &[], &output).unwrap(),
        (0, 0)
    );
}

#[test]
fn selected_curve_and_width_must_admit_distinct_checked_models() {
    let source = conversion(63, "");
    let (_, short) = inspect(&source, Curve::Goldilocks);
    assert!(!short
        .findings()
        .iter()
        .any(|finding| finding.kind() == RuleKind::NonstrictBinaryConversion));
    assert!(short.abstentions().is_empty());

    let source = conversion(64, "");
    let (_, other_curve) = inspect(&source, Curve::Bn254);
    assert!(!other_curve
        .findings()
        .iter()
        .any(|finding| finding.kind() == RuleKind::NonstrictBinaryConversion));
    assert!(other_curve.abstentions().is_empty());
}

#[test]
fn extra_generated_restriction_rejects_the_second_model() {
    let source = conversion(64, "digits[0]===0;");
    let (_, result) = inspect(&source, Curve::Goldilocks);
    assert!(result.findings().is_empty());
    assert!(result.abstentions().is_empty());
}

#[test]
fn generated_input_domain_must_contain_both_integer_encodings() {
    let source = conversion(64, "value===1;");
    let (_, admissible) = inspect(&source, Curve::Goldilocks);
    assert!(admissible
        .findings()
        .iter()
        .any(|finding| finding.kind() == RuleKind::NonstrictBinaryConversion));

    let source = conversion(64, "value===18446744069414584320;");
    let (_, excluded) = inspect(&source, Curve::Goldilocks);
    assert!(excluded.findings().is_empty());
    assert!(excluded.abstentions().is_empty());
}

#[test]
fn unrelated_failing_library_body_does_not_erase_local_conversion_evidence() {
    let source =
        format!("{}template Unrelated(){{signal output bad;bad<--1/0;}}", conversion(64, ""));
    let (_, result) = inspect(&source, Curve::Goldilocks);
    assert_eq!(
        result
            .findings()
            .iter()
            .filter(|finding| finding.kind() == RuleKind::NonstrictBinaryConversion)
            .count(),
        1
    );
}

#[test]
fn missing_relation_and_unrelated_templates_create_no_conversion_diagnostic() {
    let source = "template Decompose(){signal input value;signal output digits[1];digits[0]<--0;}";
    let (_, result) = inspect(source, Curve::Goldilocks);
    assert!(result.findings().is_empty());
    assert!(result.abstentions().is_empty());

    let source = "template Decompose(n){signal input value;}";
    let (_, result) = inspect(source, Curve::Goldilocks);
    assert!(result.findings().is_empty());
    assert!(result.abstentions().is_empty());

    let source = conversion(64, "").replace("sum===value;", "");
    let (_, result) = inspect(&source, Curve::Goldilocks);
    assert!(result.findings().is_empty());
    assert!(result.abstentions().is_empty());
}

#[test]
fn unknown_width_and_known_oversize_candidate_abstain() {
    let source = "template Decompose(n){signal input value;signal output digits[n];}";
    let (_, symbolic) = inspect(source, Curve::Goldilocks);
    assert!(symbolic.findings().is_empty());
    assert!(symbolic
        .abstentions()
        .iter()
        .any(|item| item.kind == RuleKind::NonstrictBinaryConversion));

    let source = "template Decompose(){signal input value;signal output digits[513];}";
    let (_, oversize) = inspect(source, Curve::Goldilocks);
    assert!(oversize.findings().is_empty());
    assert!(oversize
        .abstentions()
        .iter()
        .any(|item| item.kind == RuleKind::NonstrictBinaryConversion));
}

#[test]
fn incomplete_solver_and_failed_execution_cannot_emit_conversion_warning() {
    let source = conversion(64, "");
    let (_, incomplete) = inspect_with_budget(&source, Curve::Goldilocks, Some(0));
    assert!(incomplete.findings().is_empty());
    assert!(incomplete
        .abstentions()
        .iter()
        .any(|item| item.kind == RuleKind::NonstrictBinaryConversion));

    let source = conversion(64, "assert(0);");
    let (_, failed) = inspect(&source, Curve::Goldilocks);
    assert!(failed.findings().is_empty());
    assert!(failed
        .abstentions()
        .iter()
        .any(|item| item.kind == RuleKind::NonstrictBinaryConversion));
}

#[test]
fn conversion_candidates_exclude_scalar_and_rank_two_outputs() {
    for shape in ["", "[2][3]", "[0][1]", "[513][1]"] {
        let source =
            format!("template Decompose(){{signal input value;signal output bits{shape};}}");
        let (_, result) = inspect(&source, Curve::Goldilocks);
        assert!(result.findings().is_empty(), "{shape}");
        assert!(result.abstentions().is_empty(), "{shape}: {:?}", result.abstentions());
    }
}
