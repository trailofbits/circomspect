// Fixtures fail immediately on setup or analysis errors.
#![allow(clippy::allow_attributes, clippy::unwrap_used)]

use circomspect_program_analysis::application::{analyze_files, AnalysisOutput};
use program_structure::constants::Curve;
use program_structure::report::MessageCategory;

fn analyze(label: &str, source: &str) -> AnalysisOutput {
    let path = std::env::temp_dir().join(format!(
        "circomspect-source-shape-{label}-{}-{:?}.circom",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::write(&path, source).unwrap();
    let result = analyze_files(std::slice::from_ref(&path), &[], Curve::Bn254).unwrap();
    std::fs::remove_file(path).unwrap();
    result
}

fn source_errors(result: &AnalysisOutput) -> Vec<String> {
    result
        .diagnostics
        .iter()
        .chain(result.scopes.iter().flat_map(|scope| scope.reports.iter()))
        .filter(|report| *report.category() == MessageCategory::Error)
        .map(|report| format!("{}: {}", report.id(), report.message()))
        .collect()
}

#[test]
fn compiler_accepted_array_signal_assignments_have_no_source_errors() {
    for (label, assignment) in [
        ("constraint", "y<==x"),
        ("witness", "y<--x"),
        ("reverse-constraint", "x==>y"),
        ("reverse-witness", "x-->y"),
    ] {
        let source = format!(
            "pragma circom 2.2.3; template Main(n){{signal input x[n];signal output y[n];\
             {assignment};}} component main=Main(2);"
        );
        let result = analyze(label, &source);
        assert!(source_errors(&result).is_empty(), "{label}: {:?}", source_errors(&result));
    }
}

#[test]
fn compiler_accepted_component_array_assignment_has_no_source_errors() {
    let source = concat!(
        "pragma circom 2.2.3;",
        "template BitwiseOr(m){signal input a[m];signal input b[m];signal output out[m];",
        "for(var i=0;i<m;i++){out[i]<==a[i]+b[i]-a[i]*b[i];}}",
        "template OrMultiple(n,m){signal input inputs[n][m];signal output out[m];",
        "signal mids[n][m];mids[0]<==inputs[0];component ors[n-1];",
        "for(var i=0;i<n-1;i++){ors[i]=BitwiseOr(m);ors[i].a<==mids[i];",
        "ors[i].b<==inputs[i+1];mids[i+1]<==ors[i].out;}",
        "out<==mids[n-1];}component main=OrMultiple(2,2);"
    );
    let result = analyze("component-array", source);
    assert!(source_errors(&result).is_empty(), "{:?}", source_errors(&result));
}

#[test]
fn compiler_rejected_array_rank_mismatch_still_has_a_source_error() {
    let source = "pragma circom 2.2.3; template Main(n){signal input x[n];\
                  signal output y[n];y<==x[0];} component main=Main(2);";
    let result = analyze("rank-mismatch", source);
    assert_ne!(source_errors(&result).len(), 0);
}

#[test]
fn compiler_rejected_array_arithmetic_update_still_has_a_source_error() {
    let source = "pragma circom 2.2.3; template Main(){var x[2]=[1,2];\
                  x+=1;signal output y;y<==1;} component main=Main();";
    let result = analyze("arithmetic-update", source);
    assert_ne!(source_errors(&result).len(), 0);
}
