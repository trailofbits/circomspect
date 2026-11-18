// Tests inspect externally visible diagnostics for concrete Circom programs.
#![allow(clippy::allow_attributes, clippy::unwrap_used)]

use std::fs;
use std::sync::atomic::{AtomicUsize, Ordering};

use circomspect_program_analysis::application::analyze_files;
use program_structure::utils::constants::Curve;

static NEXT_CASE: AtomicUsize = AtomicUsize::new(0);

fn messages(source: &str) -> Vec<String> {
    let case = NEXT_CASE.fetch_add(1, Ordering::Relaxed);
    let directory = std::env::temp_dir()
        .join(format!("circomspect-witness-alternative-{}-{case}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    let source_path = directory.join("case.circom");
    fs::write(&source_path, source).unwrap();
    let output = analyze_files(std::slice::from_ref(&source_path), &[], Curve::Bn254).unwrap();
    fs::remove_file(source_path).unwrap();
    fs::remove_dir(directory).unwrap();
    output
        .scopes
        .into_iter()
        .flat_map(|scope| scope.reports)
        .filter(|report| report.id() == "CS0027")
        .map(|report| report.message().to_owned())
        .collect()
}

#[test]
fn alternate_root_for_witness_assignment_is_reported() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input x;signal output y;",
        "x===1;y<--x;y*(y-x)===0;}",
        "component main {public [x]}=T();"
    );
    let messages = messages(source);
    assert_eq!(messages.len(), 1, "{messages:?}");
    assert!(messages[0].contains("`y`"), "{messages:?}");
    assert!(messages[0].contains('0'), "{messages:?}");
    assert!(messages[0].contains('1'), "{messages:?}");
}

#[test]
fn simple_input_seed_finds_unfixed_counterexample() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input x;signal output y;y<--x;y*(y-x)===0;}",
        "component main {public [x]}=T();"
    );
    assert_eq!(messages(source).len(), 1);
}

#[test]
fn exact_array_target_is_named_in_counterexample() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input x;signal output y[1];",
        "x===1;y[0]<--x;y[0]*(y[0]-x)===0;}",
        "component main {public [x]}=T();"
    );
    let reports = messages(source);
    assert_eq!(reports.len(), 1, "{reports:?}");
    assert!(reports[0].contains("`y[0]`"), "{reports:?}");
}

#[test]
fn linear_constraint_excludes_alternate_root() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input x;signal output y;",
        "x===1;y<--x;y*(y-x)===0;y===x;}",
        "component main {public [x]}=T();"
    );
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn unique_quadratic_root_is_not_reported() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input x;signal output y;",
        "x===1;y<--x;(y-x)*(y-x)===0;}",
        "component main {public [x]}=T();"
    );
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn incomplete_called_scope_does_not_claim_an_alternative() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template Child(){signal input in;signal output out;out<==in;}",
        "template T(){signal input x;signal output y;component child=Child();",
        "child.in<==x;x===1;y<--x;y*(y-x)===0;}",
        "component main {public [x]}=T();"
    );
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn library_without_main_does_not_claim_an_alternative() {
    let source = "pragma circom 2.2.3;template T(){signal input x;signal output y;\
        x===1;y<--x;y*(y-x)===0;}";
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn invalid_source_does_not_claim_an_alternative() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input x;signal output y;",
        "x===1;y<--unknown;y*(y-x)===0;}",
        "component main {public [x]}=T();"
    );
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn incompatible_other_witness_prevents_a_counterexample_claim() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input x;signal output y;signal z;",
        "x===1;z<--0;z===1;y<--x;y*(y-x)===0;}",
        "component main {public [x]}=T();"
    );
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn compatible_other_witness_can_extend_the_checked_model() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input x;signal output y;signal z;",
        "x===1;z<--0;z===0;y<--x;y*(y-x)===0;}",
        "component main {public [x]}=T();"
    );
    assert_eq!(messages(source).len(), 1);
}

#[test]
fn generated_dependent_output_is_recomputed_for_alternate_model() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input x;signal output y;signal output z;",
        "x===1;y<--x;y*(y-x)===0;z<==y;}",
        "component main {public [x]}=T();"
    );
    assert_eq!(messages(source).len(), 1);
}

#[test]
fn unsupported_other_witness_expression_abstains() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input x;signal output y;signal inv;",
        "x===1;inv<--1/x;inv*x===1;y<--x;y*(y-x)===0;}",
        "component main {public [x]}=T();"
    );
    assert_eq!(messages(source), Vec::<String>::new());
}
