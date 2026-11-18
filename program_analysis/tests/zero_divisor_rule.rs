// End-to-end evidence for a zero divisor admitted by generated constraints.
#![allow(clippy::allow_attributes, clippy::unwrap_used)]

use std::fs;
use std::sync::atomic::{AtomicUsize, Ordering};

use circomspect_program_analysis::application::analyze_files;
use program_structure::utils::constants::Curve;

static NEXT_CASE: AtomicUsize = AtomicUsize::new(0);

fn messages(source: &str) -> Vec<String> {
    let case = NEXT_CASE.fetch_add(1, Ordering::Relaxed);
    let directory = std::env::temp_dir()
        .join(format!("circomspect-zero-divisor-{}-{case}", std::process::id()));
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
        .filter(|report| report.id() == "CS0029")
        .map(|report| report.message().to_owned())
        .collect()
}

fn circuit(extra: &str) -> String {
    format!(
        "pragma circom 2.2.3;template T(){{signal input x;signal output y;\
         y <-- 1 / x;x*(x-1)===0;y*x===x;{extra}}}component main=T();"
    )
}

#[test]
fn boolean_divisor_can_be_zero_in_checked_constraints() {
    let found = messages(&circuit(""));
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(found[0].contains("`x`"));
}

#[test]
fn inverse_constraint_excludes_zero() {
    let source = circuit("").replace("y*x===x;", "y*x===1;");
    assert_eq!(messages(&source), Vec::<String>::new());
}

#[test]
fn fixed_nonzero_divisor_is_not_reported() {
    assert_eq!(messages(&circuit("x===1;")), Vec::<String>::new());
}

#[test]
fn sibling_witness_assignment_must_be_consistent_at_zero() {
    assert_eq!(messages(&circuit("signal z;z <-- x+1;z===1;")).len(), 1);
    assert_eq!(messages(&circuit("signal z;z <-- x+1;z===2;")), Vec::<String>::new());
}

#[test]
fn malformed_constraint_cannot_certify_zero() {
    assert_eq!(messages(&circuit("unknown===1;")), Vec::<String>::new());
}

#[test]
fn signal_dependent_branch_does_not_certify_reaching_zero_division() {
    let source = "pragma circom 2.2.3;template T(){signal input x;signal output y;\
                  x*(x-1)===0;if(x!=0){y <-- 1/x;}y*x===x;}component main=T();";
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn caller_constraint_is_not_ignored() {
    let source = "pragma circom 2.2.3;template Child(){signal input x;signal output y;\
                  y <-- 1/x;x*(x-1)===0;y*x===x;}template Parent(){signal input x;\
                  component c=Child();c.x<==x;x===1;}component main=Parent();";
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn earlier_division_must_not_block_reaching_the_reported_site() {
    let source = "pragma circom 2.2.3;template T(){signal input x;signal input z;\
                  signal output y;y <-- (1/z)/x;x===0;z===0;y*x===0;}component main=T();";
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn unassigned_numerator_signal_withholds_a_zero_model() {
    let source = "pragma circom 2.2.3;template T(){signal input x;signal a;\
                  signal output y;y <-- a/x;x===0;y*x===0;}component main=T();";
    assert_eq!(messages(source), Vec::<String>::new());
}
