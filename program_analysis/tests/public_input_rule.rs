// Tests use temporary Circom programs and assert externally visible diagnostics.
#![allow(clippy::allow_attributes, clippy::expect_used, clippy::unwrap_used)]

use std::fs;
use std::sync::atomic::{AtomicUsize, Ordering};

use circomspect_program_analysis::application::analyze_files;
use program_structure::utils::constants::Curve;

static NEXT_CASE: AtomicUsize = AtomicUsize::new(0);

fn reports(source: &str) -> Vec<String> {
    let case = NEXT_CASE.fetch_add(1, Ordering::Relaxed);
    let directory = std::env::temp_dir()
        .join(format!("circomspect-public-input-{}-{case}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let output = analyze_files(std::slice::from_ref(&path), &[], Curve::Bn254).unwrap();
    fs::remove_file(path).unwrap();
    fs::remove_dir(directory).unwrap();
    output
        .scopes
        .into_iter()
        .flat_map(|scope| scope.reports)
        .filter(|report| report.id() == "CS0026")
        .map(|report| report.message().to_owned())
        .collect()
}

#[test]
fn public_input_without_constraint_is_reported() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input expected;signal output out;out<==1;}",
        "component main {public [expected]}=T();"
    );
    assert_eq!(reports(source), ["Public input `expected` has no generated constraint."]);
}

#[test]
fn private_input_and_constrained_public_input_are_not_reported() {
    for main in ["component main=T();", "component main {public [expected]}=T();"] {
        let body = if main.contains("public") { "expected===1;out<==1;" } else { "out<==1;" };
        let source = format!(
            "pragma circom 2.2.3;template T(){{signal input expected;signal output out;{body}}}{main}"
        );
        assert!(reports(&source).is_empty(), "{source}");
    }
}

#[test]
fn witness_only_use_does_not_bind_a_public_input() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input expected;signal output out;out<--expected;out===1;}",
        "component main {public [expected]}=T();"
    );
    assert_eq!(reports(source), ["Public input `expected` has no generated constraint."]);
}

#[test]
fn one_unused_public_array_element_is_reported() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input values[2];signal output out;out<==values[0];}",
        "component main {public [values]}=T();"
    );
    assert_eq!(reports(source), ["Public input `values[1]` has no generated constraint."]);
}

#[test]
fn generated_child_binding_constrains_the_public_input() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template Child(){signal input in;signal output out;out<==in;}",
        "template T(){signal input x;signal output out;component child=Child();",
        "child.in<==x;out<==child.out;}",
        "component main {public [x]}=T();"
    );
    assert_eq!(reports(source), Vec::<String>::new());
}

#[test]
fn unsupported_child_closure_cannot_certify_unused_public_input() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template Child(){signal input in;signal output out;out<==in;}",
        "template T(){signal input x;signal output out;component child=Child();",
        "child.in<==1;out<==child.out;}",
        "component main {public [x]}=T();"
    );
    assert_eq!(reports(source), Vec::<String>::new());
}

#[test]
fn invalid_source_cannot_certify_unused_public_input() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input x;signal output out;out<==unknown;}",
        "component main {public [x]}=T();"
    );
    assert_eq!(reports(source), Vec::<String>::new());
}

#[test]
fn oversized_public_array_abstains_from_element_claims() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template T(){signal input values[10001];signal output out;out<==1;}",
        "component main {public [values]}=T();"
    );
    assert_eq!(reports(source), Vec::<String>::new());
}
