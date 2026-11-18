// End-to-end evidence for exact weighted bit packing collisions.
#![allow(clippy::allow_attributes, clippy::panic, clippy::unwrap_used)]

use std::fs;
use std::sync::atomic::{AtomicUsize, Ordering};

use circomspect_program_analysis::application::analyze_files;
use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ProjectAnalysis, SummaryBlocker,
};
use circomspect_program_analysis::rules::{numeric, AbstentionReason, RuleContext, RuleKind};
use parser::frontend::{load_sources, Version, VersionPolicy};
use parser::hir::lift_project;
use program_structure::utils::constants::Curve;

static NEXT_CASE: AtomicUsize = AtomicUsize::new(0);

fn packer(width: usize, extra: &str) -> String {
    format!(
        "pragma circom 2.2.3;template Pack(){{signal input bits[{width}];\
         signal output packed;var sum=0;for(var i=0;i<{width};i++){{\
         bits[i]*(bits[i]-1)===0;sum+=bits[i]*(2**i);}}\
         packed<==sum;{extra}}}component main=Pack();"
    )
}

fn messages(source: &str, curve: Curve) -> Vec<String> {
    let case = NEXT_CASE.fetch_add(1, Ordering::Relaxed);
    let directory =
        std::env::temp_dir().join(format!("circomspect-bit-packing-{}-{case}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    let source_path = directory.join("case.circom");
    fs::write(&source_path, source).unwrap();
    let output = analyze_files(std::slice::from_ref(&source_path), &[], curve).unwrap();
    fs::remove_file(source_path).unwrap();
    fs::remove_dir(directory).unwrap();
    output
        .scopes
        .into_iter()
        .flat_map(|scope| scope.reports)
        .filter(|report| report.id() == "CS0028")
        .map(|report| report.message().to_owned())
        .collect()
}

#[test]
fn goldilocks_64_bit_packing_has_a_checked_collision() {
    let found = messages(&packer(64, ""), Curve::Goldilocks);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(found[0].contains("packed"));
}

#[test]
fn bn254_254_bit_packing_has_a_checked_collision() {
    let found = messages(&packer(254, ""), Curve::Bn254);
    assert_eq!(found.len(), 1, "{found:?}");
}

#[test]
fn goldilocks_63_bits_are_below_the_modulus() {
    assert_eq!(messages(&packer(63, ""), Curve::Goldilocks), Vec::<String>::new());
}

#[test]
fn extra_range_constraint_excludes_the_second_encoding() {
    assert_eq!(messages(&packer(64, "bits[0]===0;"), Curve::Goldilocks), Vec::<String>::new());
}

#[test]
fn missing_boolean_equations_do_not_certify_bit_packing() {
    let source = packer(64, "").replace("bits[i]*(bits[i]-1)===0;", "");
    assert_eq!(messages(&source, Curve::Goldilocks), Vec::<String>::new());
}

#[test]
fn wrong_weights_do_not_certify_bit_packing() {
    let source = packer(64, "").replace("2**i", "3**i");
    assert_eq!(messages(&source, Curve::Goldilocks), Vec::<String>::new());
}

#[test]
fn generated_dependent_output_is_completed_in_both_models() {
    let source = packer(64, "signal output z;z<==bits[0];");
    let found = messages(&source, Curve::Goldilocks);
    assert_eq!(found.len(), 1, "{found:?}");
}

#[test]
fn malformed_constraint_cannot_certify_a_collision() {
    let source = packer(64, "unknown===1;");
    assert_eq!(messages(&source, Curve::Goldilocks), Vec::<String>::new());
}

#[test]
fn oversized_bit_vector_refuses_the_model_search() {
    assert_eq!(messages(&packer(513, ""), Curve::Bn254), Vec::<String>::new());
}

#[test]
fn called_packer_without_closed_caller_constraints_abstains() {
    let child = packer(64, "").replace("component main=Pack();", "");
    let source = format!(
        "{child}template Parent(){{signal input bits[64];signal output packed;\
         component child=Pack();for(var i=0;i<64;i++){{child.bits[i]<==bits[i];}}\
         packed<==child.packed;bits[0]===0;}}component main=Parent();"
    );
    assert_eq!(messages(&source, Curve::Goldilocks), Vec::<String>::new());
    let case = NEXT_CASE.fetch_add(1, Ordering::Relaxed);
    let directory =
        std::env::temp_dir().join(format!("circomspect-called-pack-{}-{case}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(
        &[path],
        std::slice::from_ref(&directory),
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    let lifted = lift_project(&loaded);
    let provider = ProjectAnalysis::build(&lifted, Curve::Goldilocks).unwrap();
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main_call) =
        provider.graph().reachable_main_call(main.id(), &lifted.hir)
    else {
        panic!("main call")
    };
    let parent_evidence = provider.contexts().main_evidence(&main_call).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let parent_cfg = build_cfg(&lifted.hir, parent).unwrap();
    let parent_facts =
        provider.contexts().analyze_for_evidence(&parent_cfg, &parent_evidence, None).unwrap();
    let child_site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(child_call) =
        provider.graph().reachable_call(child_site.id(), &parent_facts)
    else {
        panic!("child call")
    };
    let child_evidence =
        provider.contexts().call_evidence(&child_call, &parent_facts, &parent_evidence).unwrap();
    let child_cfg = build_cfg(&lifted.hir, lifted.hir.definition("Pack").unwrap()).unwrap();
    let child_facts =
        provider.contexts().analyze_for_evidence(&child_cfg, &child_evidence, None).unwrap();
    let context = RuleContext::new(&child_facts, &provider, &child_evidence).unwrap();
    let rule = numeric::rules()
        .iter()
        .find(|rule| rule.kind() == RuleKind::NonInjectiveBitPacking)
        .unwrap();
    let result = rule.run(&context);
    assert!(result.findings().is_empty());
    assert!(result.abstentions().iter().any(|item| {
        item.kind == RuleKind::NonInjectiveBitPacking
            && item.reason
                == AbstentionReason::Summary(
                    [SummaryBlocker::ExternalSummary].into_iter().collect(),
                )
    }));
    fs::remove_file(loaded.files[0].path.clone()).unwrap();
    fs::remove_dir(directory).unwrap();
}
