// End-to-end evidence for binary tags contradicted by a checked satisfying model.
#![allow(clippy::allow_attributes, clippy::unwrap_used)]

use std::fmt::Write;
use std::fs;
use std::sync::atomic::{AtomicUsize, Ordering};

use circomspect_program_analysis::application::analyze_files;
use program_structure::utils::constants::Curve;

static NEXT_CASE: AtomicUsize = AtomicUsize::new(0);

fn messages(source: &str) -> Vec<String> {
    let case = NEXT_CASE.fetch_add(1, Ordering::Relaxed);
    let directory =
        std::env::temp_dir().join(format!("circomspect-binary-tag-{}-{case}", std::process::id()));
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
        .filter(|report| report.id() == "CS0030")
        .map(|report| report.message().to_owned())
        .collect()
}

#[test]
fn output_can_equal_two_under_checked_constraints() {
    let source = "pragma circom 2.2.3;template T(){signal input x;signal output {binary} y;\
                  y<==x;}component main=T();";
    let found = messages(source);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(found[0].contains("`y`"));
}

#[test]
fn intermediate_can_equal_two() {
    let source = "pragma circom 2.2.3;template T(){signal input x;signal {binary} y;\
                  signal output z;y<==x;z<==y;}component main=T();";
    assert_eq!(messages(source).len(), 1);
}

#[test]
fn unassigned_tagged_output_is_unproved_in_constraints() {
    let source = "pragma circom 2.2.3;template T(){signal output {binary} y;}\
                  component main=T();";
    let found = messages(source);
    assert_eq!(found.len(), 1, "{found:?}");
}

#[test]
fn direct_boolean_equation_proves_tag() {
    let source = "pragma circom 2.2.3;template T(){signal input x;signal output {binary} y;\
                  y<==x;y*(y-1)===0;}component main=T();";
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn inherited_boolean_constraint_proves_tag() {
    let source = "pragma circom 2.2.3;template T(){signal input x;signal output {binary} y;\
                  y<==x;x*(x-1)===0;}component main=T();";
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn generated_sum_of_binary_inputs_can_equal_two() {
    let source = "pragma circom 2.2.3;template T(){signal input x;signal input z;\
                  signal output {binary} y;y<==x+z;x*(x-1)===0;z*(z-1)===0;}\
                  component main=T();";
    assert_eq!(messages(source).len(), 1);
}

#[test]
fn many_tags_share_one_checked_constraint_scope() {
    let mut source = String::from("pragma circom 2.2.3;template T(){signal input x;");
    for index in 0..64 {
        write!(source, "signal {{binary}} t{index};t{index}<==x;").unwrap();
    }
    source.push_str("}component main=T();");
    assert_eq!(messages(&source).len(), 64);
}

#[test]
fn one_constrained_input_does_not_hide_another_tags_counterexample() {
    let source = "pragma circom 2.2.3;template T(){signal input x;signal input w;\
                  signal output {binary} protected;signal output {binary} open;\
                  protected<==x;open<==w;x*(x-1)===0;}component main=T();";
    let found = messages(source);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(found[0].contains("`open`"));
}

#[test]
fn witness_sum_can_equal_two() {
    let source = "pragma circom 2.2.3;template T(){signal input x;signal input z;\
                  signal output {binary} y;y<--x+z;x*(x-1)===0;z*(z-1)===0;}\
                  component main=T();";
    assert_eq!(messages(source).len(), 1);
}

#[test]
fn witness_only_assignment_must_agree_with_counterexample() {
    let source = "pragma circom 2.2.3;template T(){signal input x;signal output {binary} y;\
                  y<--x;x*(x-1)===0;}component main=T();";
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn input_tag_is_a_caller_precondition() {
    let source = "pragma circom 2.2.3;template T(){signal input {binary} x;\
                  signal output y;y<==x;}component main=T();";
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn unrelated_tag_is_ignored() {
    let source = "pragma circom 2.2.3;template T(){signal input x;signal output {maxbit} y;\
                  y<==x;}component main=T();";
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn caller_constraint_withholds_child_only_counterexample() {
    let source = "pragma circom 2.2.3;template Child(){signal input x;\
                  signal output {binary} y;y<==x;}template Parent(){signal input x;\
                  component c=Child();c.x<==x;x*(x-1)===0;}component main=Parent();";
    assert_eq!(messages(source), Vec::<String>::new());
}

#[test]
fn malformed_scope_cannot_certify_counterexample() {
    let source = "pragma circom 2.2.3;template T(){signal input x;signal output {binary} y;\
                  y<==x;unknown===1;}component main=T();";
    assert_eq!(messages(source), Vec::<String>::new());
}
