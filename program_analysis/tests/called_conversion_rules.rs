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
use circomspect_program_analysis::interprocedural::{CallOwner, CallReachability, ProjectAnalysis};
use circomspect_program_analysis::rules::{numeric, RuleContext, RuleKind, RuleResult, SourceMap};
use parser::hir::lift_project;
use parser::frontend::{load_sources, LoadedProject, Version, VersionPolicy};
use program_structure::report::MessageCategory;
use program_structure::utils::constants::Curve;
use serde_json::Value;

fn conversion(width: usize, parent_extra: &str, child_extra: &str) -> String {
    format!(
        "template Convert(n){{signal input in;signal output bits[n];var sum=0;\
         for(var i=0;i<n;i++){{bits[i]<--(in >> i)&1;bits[i]*(bits[i]-1)===0;\
         sum+=bits[i]*(2**i);}}in===sum;{child_extra}}}\
         template Parent(){{signal input x;component c=Convert({width});c.in<==x;{parent_extra}}}\
         component main=Parent();"
    )
}

fn inspect(source: &str, curve: Curve, budget: Option<usize>) -> (LoadedProject, RuleResult) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-called-conversion-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    let provider = ProjectAnalysis::build(&lifted, curve).unwrap();
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(main.id(), &lifted.hir)
    else {
        panic!("main call must be reachable");
    };
    let evidence = provider.contexts().main_evidence(&call).unwrap();
    let definition = lifted.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, budget).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    let rule = numeric::rules()
        .iter()
        .find(|rule| rule.kind() == RuleKind::NonstrictBinaryConversion)
        .unwrap();
    (loaded, rule.run(&context))
}

fn findings(result: &RuleResult) -> usize {
    result
        .findings()
        .iter()
        .filter(|finding| finding.kind() == RuleKind::NonstrictBinaryConversion)
        .count()
}

#[test]
fn called_conversion_reports_complete_parent_child_pair_and_renders_cs0010() {
    let source = conversion(64, "", "");
    let (loaded, result) = inspect(&source, Curve::Goldilocks, None);
    assert_eq!(findings(&result), 1, "{:?}", result.abstentions());
    let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
    let finding = &result.findings()[0];
    let report = finding.to_report(&sources).unwrap();
    assert_eq!(report.id(), "CS0010");
    assert_eq!(*report.category(), MessageCategory::Warning);
    assert!(report.message().contains("same field input"));
    assert!(report.message().contains("distinct 64-bit vectors"));
    assert_eq!(report.primary()[0].range.start, source.find("Convert(64)").unwrap());
    let output = loaded.files[0].path.with_extension("sarif.json");
    assert_eq!(
        support::render(result.findings(), &sources, MessageCategory::Warning, &[], &output)
            .unwrap(),
        (1, 1)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
    assert_eq!(sarif["runs"][0]["results"][0]["ruleId"], "CS0010");
    assert_eq!(sarif["runs"][0]["results"][0]["level"], "warning");
    assert_eq!(
        support::render(result.findings(), &sources, MessageCategory::Error, &[], &output).unwrap(),
        (0, 0)
    );
    assert_eq!(
        support::render(
            result.findings(),
            &sources,
            MessageCategory::Warning,
            &["CS0010"],
            &output
        )
        .unwrap(),
        (0, 0)
    );
    let hidden = SourceMap::from_loaded(&loaded, &[]).unwrap();
    assert_eq!(
        support::render(result.findings(), &hidden, MessageCategory::Warning, &[], &output)
            .unwrap(),
        (0, 0)
    );
}

#[test]
fn called_conversion_near_misses_and_incomplete_evidence_do_not_warn() {
    let (_, short) = inspect(&conversion(63, "", ""), Curve::Goldilocks, None);
    assert_eq!(findings(&short), 0);
    assert!(short.abstentions().is_empty());

    let (_, constrained) = inspect(&conversion(64, "c.bits[0]===0;", ""), Curve::Goldilocks, None);
    assert_eq!(findings(&constrained), 0);
    assert!(constrained.abstentions().is_empty());

    let (_, missing) =
        inspect(&conversion(64, "", "").replace("c.in<==x;", ""), Curve::Goldilocks, None);
    assert_eq!(findings(&missing), 0);
    assert!(missing
        .abstentions()
        .iter()
        .any(|item| item.kind == RuleKind::NonstrictBinaryConversion));

    let (_, witness_only) =
        inspect(&conversion(64, "", "").replace("c.in<==x;", "c.in<--x;"), Curve::Goldilocks, None);
    assert_eq!(findings(&witness_only), 0);
    assert!(witness_only
        .abstentions()
        .iter()
        .any(|item| item.kind == RuleKind::NonstrictBinaryConversion));

    let (_, incomplete) = inspect(&conversion(64, "", ""), Curve::Goldilocks, Some(0));
    assert_eq!(findings(&incomplete), 0);
    assert!(incomplete
        .abstentions()
        .iter()
        .any(|item| item.kind == RuleKind::NonstrictBinaryConversion));
}

#[test]
fn clean_non_candidate_and_unrelated_incomplete_library_keep_scopes_separate() {
    let source = "template Convert(n){signal input in;signal output out;out<==in;}\
                  template Parent(){signal input x;component c=Convert(1);c.in<==x;}\
                  component main=Parent();";
    let (_, clean) = inspect(source, Curve::Goldilocks, None);
    assert_eq!(findings(&clean), 0);
    assert!(clean.abstentions().is_empty());

    let source = conversion(64, "", "").replace(
        "component main=Parent();",
        "function Broken(){return Missing();}component main=Parent();",
    );
    let (_, independent) = inspect(&source, Curve::Goldilocks, None);
    assert_eq!(findings(&independent), 1, "{:?}", independent.abstentions());
}

#[test]
fn canonical_bn254_called_conversion_reports_two_checked_models() {
    let source = conversion(254, "", "");
    let (_, result) = inspect(&source, Curve::Bn254, None);
    assert_eq!(findings(&result), 1, "{:?}", result.abstentions());
}
