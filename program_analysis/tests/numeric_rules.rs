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

use std::collections::BTreeSet;
use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ProjectAnalysis, SummaryBlocker,
};
use circomspect_program_analysis::rules::{
    run_registered, AbstentionReason, Finding, RuleContext, RuleKind, RuleResult, SourceMap,
};
use num_bigint_dig::BigInt;
use parser::hir::lift_project;
use parser::frontend::{load_sources, LoadedProject, Version, VersionPolicy};
use program_structure::report::MessageCategory;
use program_structure::utils::constants::{Curve, UsefulConstants};
use serde_json::Value;

const BN254_MODULUS: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495617";
const BN254_LAST: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495616";

fn inspect(source: &str, curve: Curve, definition: &str) -> (LoadedProject, RuleResult) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-numeric-{}-{:?}",
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
    let definition = lifted.hir.definition(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let summaries = ProjectAnalysis::build(&lifted, curve).unwrap();
    let evidence = summaries.contexts().symbolic_root(definition).unwrap();
    let facts = summaries.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &summaries, &evidence).unwrap();
    let result = run_registered(&context).unwrap();
    (loaded, result)
}

fn inspect_call(
    source: &str,
    curve: Curve,
    parent: &str,
    child: &str,
) -> (LoadedProject, RuleResult) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-numeric-call-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty());
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    let parent = lifted.hir.definition(parent).unwrap();
    let child = lifted.hir.definition(child).unwrap();
    let summaries = ProjectAnalysis::build(&lifted, curve).unwrap();
    let parent_evidence = summaries.contexts().symbolic_root(parent).unwrap();
    let parent_cfg = build_cfg(&lifted.hir, parent).unwrap();
    let parent_facts =
        summaries.contexts().analyze_for_evidence(&parent_cfg, &parent_evidence, None).unwrap();
    let site = summaries.graph().calls_from(CallOwner::Definition(parent))[0];
    let call = match summaries.graph().reachable_call(site.id(), &parent_facts) {
        CallReachability::Reachable(call) => call,
        CallReachability::Unreachable => panic!("child call is unreachable"),
        CallReachability::Unavailable(blocker) => panic!("child call blocked: {blocker:?}"),
    };
    assert_eq!(call.callee(), child);
    let evidence =
        summaries.contexts().call_evidence(&call, &parent_facts, &parent_evidence).unwrap();
    let cfg = build_cfg(&lifted.hir, child).unwrap();
    let facts = summaries.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &summaries, &evidence).unwrap();
    (loaded, run_registered(&context).unwrap())
}

fn inspect_main(source: &str, curve: Curve) -> RuleResult {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-numeric-main-{}-{:?}",
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
    let provider = ProjectAnalysis::build(&lifted, curve).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &lifted.hir)
    else {
        panic!("reachable main")
    };
    let evidence = provider.contexts().main_evidence(&call).unwrap();
    let cfg = build_cfg(&lifted.hir, evidence.context().definition()).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    run_registered(&context).unwrap()
}

fn numeric_findings(result: &RuleResult) -> Vec<Finding> {
    let mut findings = Vec::new();
    for finding in result.findings() {
        if circomspect_program_analysis::rules::numeric::KINDS.contains(&finding.kind()) {
            findings.push(finding.clone());
        }
    }
    findings
}

fn kinds(result: &RuleResult) -> Vec<RuleKind> {
    numeric_findings(result).iter().map(Finding::kind).collect()
}

fn first_message(loaded: &LoadedProject, result: &RuleResult) -> String {
    let sources = SourceMap::from_loaded(loaded, &[loaded.files[0].id]).unwrap();
    numeric_findings(result)[0].to_report(&sources).unwrap().message().clone()
}

fn assert_rendered(loaded: &LoadedProject, result: &RuleResult, kind: RuleKind) {
    let source = &loaded.files[0];
    let sources = SourceMap::from_loaded(loaded, &[source.id]).unwrap();
    let findings = result
        .findings()
        .iter()
        .filter(|finding| finding.kind() == kind)
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(findings.len(), 1);
    let report = findings[0].to_report(&sources).unwrap();
    assert_eq!(report.id(), kind.code().id());
    assert_eq!(report.primary().len(), 1);
    assert!(report.primary()[0].range.end > report.primary()[0].range.start);
    let output = source.path.with_extension("sarif.json");
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Info, &[], &output).unwrap(),
        (1, 1)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(output).unwrap()).unwrap();
    let item = &sarif["runs"][0]["results"][0];
    assert_eq!(item["ruleId"], kind.code().id());
    assert_eq!(item["level"], kind.category().to_level());
}

#[test]
fn complement_reports_only_reachable_resolved_expression_with_selected_curve() {
    let (loaded, result) = inspect("template T(){var x=~1;}", Curve::Goldilocks, "T");
    assert_eq!(kinds(&result), [RuleKind::BitwiseComplement]);
    assert!(first_message(&loaded, &result).contains("Goldilocks"));
    assert_rendered(&loaded, &result, RuleKind::BitwiseComplement);
    let source = &loaded.files[0];
    let sources = SourceMap::from_loaded(&loaded, &[source.id]).unwrap();
    let output = source.path.with_extension("sarif.json");
    assert_eq!(
        support::render(&numeric_findings(&result), &sources, MessageCategory::Info, &[], &output)
            .unwrap(),
        (1, 1)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(output).unwrap()).unwrap();
    assert_eq!(sarif["runs"][0]["results"][0]["ruleId"], "CS0004");
    assert_eq!(sarif["runs"][0]["results"][0]["level"], "note");

    let (_, near) = inspect("template T(){var x=!1;}", Curve::Goldilocks, "T");
    assert!(!kinds(&near).contains(&RuleKind::BitwiseComplement));
    let (_, dead) = inspect("template T(){if(0){var x=~1;}}", Curve::Goldilocks, "T");
    assert!(!kinds(&dead).contains(&RuleKind::BitwiseComplement));
    let (_, symbolic) = inspect("template T(n){if(n){var x=~1;}}", Curve::Goldilocks, "T");
    assert!(!kinds(&symbolic).contains(&RuleKind::BitwiseComplement));
    assert!(symbolic.abstentions().iter().any(|a| a.kind == RuleKind::BitwiseComplement));
    let (_, variable) = inspect("template T(n){var x=~n;}", Curve::Goldilocks, "T");
    assert!(
        kinds(&variable).contains(&RuleKind::BitwiseComplement),
        "{:?}",
        variable.abstentions()
    );
}

#[test]
fn conditional_requires_one_boolean_on_every_reachable_execution() {
    let (loaded, yes) = inspect("template T(){if(1){var x=1;}}", Curve::Bn254, "T");
    assert_eq!(kinds(&yes), [RuleKind::ConstantConditional]);
    assert_rendered(&loaded, &yes, RuleKind::ConstantConditional);
    let (loaded, no) = inspect("template T(){if(0){var x=1;}}", Curve::Bn254, "T");
    assert_eq!(kinds(&no), [RuleKind::ConstantConditional]);
    assert!(first_message(&loaded, &no).contains("false"));
    let (_, symbolic) = inspect("template T(n){if(n){var x=1;}}", Curve::Bn254, "T");
    assert!(!kinds(&symbolic).contains(&RuleKind::ConstantConditional));
    assert!(symbolic.abstentions().iter().any(|a| a.kind == RuleKind::ConstantConditional));
    let (_, nested) = inspect("template T(n){if(n){if(1){var x=1;}}}", Curve::Bn254, "T");
    assert!(!kinds(&nested).contains(&RuleKind::ConstantConditional));
    assert!(nested.abstentions().iter().any(|a| a.kind == RuleKind::ConstantConditional));
}

#[test]
fn arithmetic_reports_proved_wraparound_only() {
    let source = format!("template T(){{var x={BN254_LAST}+1;}}");
    let (loaded, wrap) = inspect(&source, Curve::Bn254, "T");
    assert_eq!(kinds(&wrap), [RuleKind::FieldArithmetic]);
    assert!(first_message(&loaded, &wrap).contains("modulo"));
    assert_rendered(&loaded, &wrap, RuleKind::FieldArithmetic);
    let (_, near) = inspect("template T(){var x=1+1;}", Curve::Bn254, "T");
    assert!(!kinds(&near).contains(&RuleKind::FieldArithmetic));
    let source = format!("template T(){{var x={BN254_LAST}+0;}}");
    let (_, boundary) = inspect(&source, Curve::Bn254, "T");
    assert!(!kinds(&boundary).contains(&RuleKind::FieldArithmetic));
    let (_, symbolic) = inspect("template T(n){var x=n+1;}", Curve::Bn254, "T");
    assert!(!kinds(&symbolic).contains(&RuleKind::FieldArithmetic));
    assert!(symbolic.abstentions().iter().any(|a| a.kind == RuleKind::FieldArithmetic));
    let (loaded, negative) = inspect("template T(){var x=0-1;}", Curve::Bn254, "T");
    assert_eq!(kinds(&negative), [RuleKind::FieldArithmetic]);
    assert_rendered(&loaded, &negative, RuleKind::FieldArithmetic);
    let source = format!("template T(){{var x={BN254_MODULUS}+1;}}");
    let (_, canonical) = inspect(&source, Curve::Bn254, "T");
    assert!(!kinds(&canonical).contains(&RuleKind::FieldArithmetic));
}

#[test]
fn comparison_requires_proved_signed_unsigned_disagreement() {
    let source = format!("template T(){{var x={BN254_LAST}<0;}}");
    let (loaded, different) = inspect(&source, Curve::Bn254, "T");
    assert_eq!(kinds(&different), [RuleKind::FieldComparison]);
    assert!(first_message(&loaded, &different).contains("signed"));
    assert_rendered(&loaded, &different, RuleKind::FieldComparison);
    let (_, near) = inspect("template T(){var x=1<2;}", Curve::Bn254, "T");
    assert!(!kinds(&near).contains(&RuleKind::FieldComparison));
    let (_, symbolic) = inspect("template T(n){var x=n<0;}", Curve::Bn254, "T");
    assert!(!kinds(&symbolic).contains(&RuleKind::FieldComparison));
    assert!(symbolic.abstentions().iter().any(|a| a.kind == RuleKind::FieldComparison));
    let half = UsefulConstants::new(&Curve::Bn254).prime().clone() / 2;
    let source = format!("template T(){{var x={half}<0;}}");
    let (_, boundary) = inspect(&source, Curve::Bn254, "T");
    assert!(!kinds(&boundary).contains(&RuleKind::FieldComparison));
    let source = format!("template T(){{var x={}<0;}}", half + 1);
    let (_, boundary) = inspect(&source, Curve::Bn254, "T");
    assert!(kinds(&boundary).contains(&RuleKind::FieldComparison));
}

#[test]
fn bn254_literal_only_warns_on_incompatible_selected_curve() {
    let source = format!("template T(){{var x={BN254_MODULUS};}}");
    let (loaded, other) = inspect(&source, Curve::Bls12_381, "T");
    assert_eq!(kinds(&other), [RuleKind::Bn254SpecificCircuit]);
    assert_rendered(&loaded, &other, RuleKind::Bn254SpecificCircuit);
    let (_, same) = inspect(&source, Curve::Bn254, "T");
    assert!(!kinds(&same).contains(&RuleKind::Bn254SpecificCircuit));
    let (_, near) = inspect("template T(){var x=12345;}", Curve::Bls12_381, "T");
    assert!(!kinds(&near).contains(&RuleKind::Bn254SpecificCircuit));
    let source = format!("template T(n){{if(n){{var x={BN254_MODULUS};}}}}");
    let (_, opaque) = inspect(&source, Curve::Bls12_381, "T");
    assert!(!kinds(&opaque).contains(&RuleKind::Bn254SpecificCircuit));
    assert!(opaque.abstentions().iter().any(|a| a.kind == RuleKind::Bn254SpecificCircuit));

    let source = format!(
        "template Child(){{var p={BN254_MODULUS};}}\
         template Parent(){{component c=Child();}}"
    );
    let (loaded, called) = inspect_call(&source, Curve::Bls12_381, "Parent", "Child");
    assert_eq!(kinds(&called), [RuleKind::Bn254SpecificCircuit]);
    let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
    let report = numeric_findings(&called)[0].to_report(&sources).unwrap();
    assert_eq!(report.secondary().len(), 1);
    let call_start = source.rfind("Child()").unwrap();
    assert_eq!(report.secondary()[0].range, call_start..call_start + "Child()".len());
    assert_eq!(report.secondary()[0].message, "Validated call path step 1");
    assert_rendered(&loaded, &called, RuleKind::Bn254SpecificCircuit);
}

#[test]
fn bn254_constant_requires_a_template_origin() {
    let source = format!("function F(){{return {BN254_MODULUS};}}");
    let (_, bare_function) = inspect(&source, Curve::Bls12_381, "F");
    assert!(!kinds(&bare_function).contains(&RuleKind::Bn254SpecificCircuit));
    let source = format!("bus B(){{signal x;var n={BN254_MODULUS};}}");
    let (_, bare_bus) = inspect(&source, Curve::Bls12_381, "B");
    assert!(!kinds(&bare_bus).contains(&RuleKind::Bn254SpecificCircuit));
}

#[test]
fn division_requires_exact_input_and_complete_zero_constraint_incidence() {
    let (loaded, bare) =
        inspect("template T(){signal input in;signal output out;out <-- 1/in;}", Curve::Bn254, "T");
    assert_eq!(kinds(&bare), [RuleKind::UnconstrainedDivision]);
    assert_rendered(&loaded, &bare, RuleKind::UnconstrainedDivision);
    let (_, constrained) = inspect(
        "template T(){signal input in;signal output out;signal inv;\
         inv <-- 1/in;out <-- 1/in;in*inv===1;}",
        Curve::Bn254,
        "T",
    );
    assert!(!kinds(&constrained).contains(&RuleKind::UnconstrainedDivision));
    let (_, transitive) = inspect(
        "template T(){signal input in;signal output out;signal inv;\
         var t=in;inv <-- 1/in;out <-- 1/in;t*inv===1;}",
        Curve::Bn254,
        "T",
    );
    assert!(!kinds(&transitive).contains(&RuleKind::UnconstrainedDivision));
    let (_, wrong_operator) =
        inspect("template T(){signal input in;signal output out;out <== 1/in;}", Curve::Bn254, "T");
    assert!(!kinds(&wrong_operator).contains(&RuleKind::UnconstrainedDivision));
    let (_, non_access) = inspect(
        "template T(){signal input in;signal output out;out <-- 1/(in+1);}",
        Curve::Bn254,
        "T",
    );
    assert!(!kinds(&non_access).contains(&RuleKind::UnconstrainedDivision));
    assert!(non_access.abstentions().iter().any(|a| a.kind == RuleKind::UnconstrainedDivision));
    let (_, exact_array) = inspect(
        "template T(){signal input in[2];signal output out;out <-- 1/in[0];}",
        Curve::Bn254,
        "T",
    );
    assert!(kinds(&exact_array).contains(&RuleKind::UnconstrainedDivision));
    let (_, symbolic_array) = inspect(
        "template T(i){signal input in[2];signal output out;out <-- 1/in[i];}",
        Curve::Bn254,
        "T",
    );
    assert!(!kinds(&symbolic_array).contains(&RuleKind::UnconstrainedDivision));
    assert!(
        symbolic_array.abstentions().iter().any(|a| a.kind == RuleKind::UnconstrainedDivision),
        "{:?}",
        symbolic_array.abstentions()
    );
}

#[test]
fn called_division_does_not_claim_zero_incidence_without_incoming_closure() {
    let source = "template D(){signal input x;signal output out;out <-- 1/x;}\
                  template T(){signal input x;signal inv;inv<--1/x;x*inv===1;\
                  component d=D();d.x<==x;}component main=T();";
    let (_, called) = inspect_call(source, Curve::Bn254, "T", "D");
    assert!(!kinds(&called).contains(&RuleKind::UnconstrainedDivision));
    assert!(called.abstentions().iter().any(|item| {
        item.kind == RuleKind::UnconstrainedDivision
            && item.reason
                == AbstentionReason::Summary(BTreeSet::from([SummaryBlocker::ExternalSummary]))
    }));
}

#[test]
fn main_division_retains_local_zero_incidence_rule() {
    let source = "template D(){signal input x;signal output out;out <-- 1/x;}component main=D();";
    let result = inspect_main(source, Curve::Bn254);
    assert!(kinds(&result).contains(&RuleKind::UnconstrainedDivision));
}

#[test]
fn definitions_without_a_conversion_port_candidate_are_quiet() {
    let (_, no_main) = inspect("template T(n){signal input x;}", Curve::Bn254, "T");
    assert!(!kinds(&no_main).contains(&RuleKind::NonstrictBinaryConversion));
    assert!(!no_main
        .abstentions()
        .iter()
        .any(|item| item.kind == RuleKind::NonstrictBinaryConversion));

    let source = "template T(n){signal input x;} component main=T(1);";
    let (_, library) = inspect(source, Curve::Bn254, "T");
    assert!(!kinds(&library).contains(&RuleKind::NonstrictBinaryConversion));
    assert!(!library
        .abstentions()
        .iter()
        .any(|item| item.kind == RuleKind::NonstrictBinaryConversion));

    let main = inspect_main(source, Curve::Bn254);
    assert!(!kinds(&main).contains(&RuleKind::NonstrictBinaryConversion));
    assert!(!main
        .abstentions()
        .iter()
        .any(|item| item.kind == RuleKind::NonstrictBinaryConversion));
}

#[test]
fn certified_call_specialization_changes_numeric_decisions() {
    let source = "template Child(n){if(n){var x=1;}}\
                  template Parent(){component c=Child(1);}";
    let (_, result) = inspect_call(source, Curve::Bn254, "Parent", "Child");
    assert!(kinds(&result).contains(&RuleKind::ConstantConditional));
    let source = "template Child(n){if(n){var x=1;}}\
                  template Parent(){component c=Child(0);}";
    let (_, result) = inspect_call(source, Curve::Bn254, "Parent", "Child");
    assert!(kinds(&result).contains(&RuleKind::ConstantConditional));
    let source = "template Child(n){if(n){var x=1;}}\
                  template Parent(m){component c=Child(m);}";
    let loaded = inspect(source, Curve::Bn254, "Child").1;
    assert!(!kinds(&loaded).contains(&RuleKind::ConstantConditional));
}

#[test]
fn numeric_findings_obey_level_allow_and_root_filters() {
    let source = "template T(){var x=~1;}";
    let (loaded, result) = inspect(source, Curve::Goldilocks, "T");
    let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
    let output = loaded.files[0].path.with_extension("sarif.json");
    assert_eq!(
        support::render(
            &numeric_findings(&result),
            &sources,
            MessageCategory::Warning,
            &[],
            &output
        )
        .unwrap(),
        (0, 0)
    );
    assert_eq!(
        support::render(
            &numeric_findings(&result),
            &sources,
            MessageCategory::Info,
            &["CS0004"],
            &output
        )
        .unwrap(),
        (0, 0)
    );

    let directory = std::env::temp_dir().join(format!(
        "circomspect-numeric-root-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let root = directory.join("root.circom");
    let library = directory.join("library.circom");
    fs::write(&root, "include \"library.circom\"; template Root(){}").unwrap();
    fs::write(&library, source).unwrap();
    let loaded = load_sources(&[root], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty());
    let definition = lifted.hir.definition("T").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let summaries = ProjectAnalysis::build(&lifted, Curve::Goldilocks).unwrap();
    let evidence = summaries.contexts().symbolic_root(definition).unwrap();
    let facts = summaries.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &summaries, &evidence).unwrap();
    let result = run_registered(&context).unwrap();
    assert!(kinds(&result).contains(&RuleKind::BitwiseComplement));
    let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
    assert_eq!(
        support::render(&numeric_findings(&result), &sources, MessageCategory::Info, &[], &output)
            .unwrap(),
        (0, 0)
    );
}

#[test]
fn independent_numeric_events_after_known_failure_do_not_warn() {
    for (declaration, end) in [("template T()", ""), ("function T()", "return 7;")] {
        for (prefix, should_emit) in [
            ("assert(0);", false),
            ("var z=1/0;", false),
            ("assert(1);", true),
            ("var z=1/1;", true),
            ("if(0){assert(0);}", true),
        ] {
            let source = format!("{declaration}{{{prefix}var x=~1;var y=0-1;{end}}}");
            let (_, result) = inspect(&source, Curve::Bn254, "T");
            for kind in [RuleKind::BitwiseComplement, RuleKind::FieldArithmetic] {
                assert_eq!(kinds(&result).contains(&kind), should_emit, "{source}: {kind:?}");
            }
        }
    }
}

#[test]
fn independent_numeric_scope_guard_retains_typed_abstentions_and_unknown_controls() {
    for prefix in ["assert(0);", "var z=1/0;"] {
        let source = format!("template T(){{{prefix}var x=~1;var y=0-1;}}");
        let (_, result) = inspect(&source, Curve::Bn254, "T");
        for kind in [RuleKind::BitwiseComplement, RuleKind::FieldArithmetic] {
            assert!(result.abstentions().iter().any(|item| {
                let AbstentionReason::Summary(reasons) = &item.reason else { return false };
                item.kind == kind && !reasons.is_empty()
            }));
        }
    }
    let source = "template T(){signal input p;assert(p);var x=~1;var y=0-1;}";
    let (_, result) = inspect(source, Curve::Bn254, "T");
    assert!(kinds(&result).contains(&RuleKind::BitwiseComplement), "{source}");
    assert!(kinds(&result).contains(&RuleKind::FieldArithmetic), "{source}");
    for source in [
        "pragma custom_templates;template custom T(){var x=~1;var y=0-1;}",
        "template extern_c T(){var x=~1;var y=0-1;}",
    ] {
        let (_, result) = inspect(source, Curve::Bn254, "T");
        assert!(!kinds(&result).contains(&RuleKind::BitwiseComplement), "{source}");
        assert!(!kinds(&result).contains(&RuleKind::FieldArithmetic), "{source}");
    }
}

#[test]
fn division_requires_source_ready_and_supported_generated_constraints() {
    let invalid = [
        "template T(){signal input divisor;signal s;signal output out;out<--s/divisor;}",
        "template T(){signal input divisor;signal input a;signal input b;signal input c;\
         signal output out;out<--1/divisor;a*b+a*c===0;}",
    ];
    for source in invalid {
        let (_, result) = inspect(source, Curve::Bn254, "T");
        assert!(
            !kinds(&result).contains(&RuleKind::UnconstrainedDivision),
            "invalid source must not issue division warning: {source}"
        );
        assert!(result
            .abstentions()
            .iter()
            .any(|item| { item.kind == RuleKind::UnconstrainedDivision }));
    }
    let (_, ready) = inspect(
        "template T(){signal input divisor;signal s;signal output out;s<--1;out<--s/divisor;}",
        Curve::Bn254,
        "T",
    );
    assert!(kinds(&ready).contains(&RuleKind::UnconstrainedDivision));
}

#[test]
fn independent_division_array_element_requires_bounded_ready_source() {
    let (_, valid) = inspect(
        "template T(){signal input divisor[2];signal output out;out<--1/divisor[1];}",
        Curve::Bn254,
        "T",
    );
    assert!(kinds(&valid).contains(&RuleKind::UnconstrainedDivision));
    let (_, invalid) = inspect(
        "template T(){signal input divisor[2];signal numerator[2];signal output out;\
         out<--numerator[0]/divisor[1];}",
        Curve::Bn254,
        "T",
    );
    assert!(!kinds(&invalid).contains(&RuleKind::UnconstrainedDivision));
    assert!(invalid.abstentions().iter().any(|item| item.kind == RuleKind::UnconstrainedDivision));
}

#[test]
fn warning_corpus_distinguishes_the_field_prime_from_the_old_nearby_literal() {
    let cases = [
        ("bn254_specific", Curve::Bls12_381, RuleKind::Bn254SpecificCircuit),
        ("field_arithmetic", Curve::Bn254, RuleKind::FieldArithmetic),
        ("field_comparison", Curve::Bn254, RuleKind::FieldComparison),
    ];
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../tests/warnings/cases");
    for (name, curve, kind) in cases {
        let source = fs::read_to_string(root.join(format!("{name}_emit.circom"))).unwrap();
        let result = inspect_main(&source, curve.clone());
        assert!(!kinds(&result).contains(&kind), "old literal: {name}");
        let source = fs::read_to_string(root.join(format!("{name}_boundary_emit.circom"))).unwrap();
        let result = inspect_main(&source, curve);
        assert!(kinds(&result).contains(&kind), "actual field boundary: {name}");
    }
}

#[test]
fn all_supported_curves_preserve_canonical_arithmetic_boundaries() {
    for curve in [Curve::Bn254, Curve::Bls12_381, Curve::Goldilocks] {
        let prime = UsefulConstants::new(&curve).prime().clone();
        let last = &prime - 1;
        let half: BigInt = &prime / 2;
        for (expression, expected) in [
            (format!("{last}+0"), 0),
            (format!("{last}+1"), 1),
            (format!("{half}*2"), 0),
            (format!("{}*2", &half + 1), 1),
            (format!("{prime}+1"), 0),
            ("0-1".into(), 1),
        ] {
            let source = format!("template Check(){{var x={expression};}}");
            let (_, result) = inspect(&source, curve.clone(), "Check");
            assert_eq!(
                kinds(&result).iter().filter(|kind| **kind == RuleKind::FieldArithmetic).count(),
                expected,
                "{curve}: {source}"
            );
        }
    }
}

#[test]
fn every_relational_operator_obeys_the_signed_half_field_boundary() {
    for curve in [Curve::Bn254, Curve::Bls12_381, Curve::Goldilocks] {
        let prime = UsefulConstants::new(&curve).prime().clone();
        let half: BigInt = &prime / 2;
        for operator in ["<", "<=", ">", ">="] {
            for (operand, expected) in [(&half, 0), (&(&half + 1), 1)] {
                let source = format!("template Check(){{var x={operand}{operator}0;}}");
                let (_, result) = inspect(&source, curve.clone(), "Check");
                assert_eq!(
                    kinds(&result)
                        .iter()
                        .filter(|kind| **kind == RuleKind::FieldComparison)
                        .count(),
                    expected,
                    "{curve}: {source}"
                );
            }
        }
    }
}
