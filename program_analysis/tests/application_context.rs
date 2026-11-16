// Fixtures fail immediately on setup or analysis errors.
#![allow(clippy::allow_attributes, clippy::expect_used, clippy::unwrap_used)]

use circomspect_program_analysis::application::{analyze_files, AnalysisOutput};
use program_structure::constants::Curve;
use program_structure::report::Report;

fn analyze(source: &str) -> AnalysisOutput {
    let path = std::env::temp_dir().join(format!(
        "circomspect-context-{}-{:?}.circom",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::write(&path, format!("pragma circom 2.2.3;{source}")).unwrap();
    let output = analyze_files(std::slice::from_ref(&path), &[], Curve::Bn254).unwrap();
    std::fs::remove_file(path).unwrap();
    output
}

fn findings<'a>(output: &'a AnalysisOutput, code: &str) -> Vec<&'a Report> {
    output.scopes.iter().flat_map(|scope| &scope.reports).filter(|item| item.id() == code).collect()
}

#[test]
fn unrelated_parameters_do_not_annotate_unused_values() {
    for value in ["1", "1+2"] {
        let output = analyze(&format!(
            "template Child(n){{var dead={value};signal output out;out<==n;}}\
            template Main(){{component a=Child(1);component b=Child(2);}}component main=Main();"
        ));
        for code in ["CS0006", "CS0008"] {
            let unused = findings(&output, code);
            assert_eq!(unused.len(), 1);
            assert!(unused[0].secondary().is_empty(), "{code}: {:?}", unused[0].secondary());
        }
    }
}

#[test]
fn final_loop_update_names_the_unused_iteration_without_repeating_contexts() {
    let output = analyze(
        "template Child(n){var e2=1;var total=0;\
        for(var i=0;i<n;i++){total+=e2;e2=e2+e2;}signal output out;out<==total;}\
        template Main(){component a=Child(1);component b=Child(2);component c=Child(3);}\
        component main=Main();",
    );
    let unused = findings(&output, "CS0006");
    assert_eq!(unused.len(), 1);
    assert!(unused[0].message().contains("e2"));
    assert_eq!(unused[0].primary()[0].message, "The final loop update to this variable is unused.");
    assert!(unused[0].secondary().is_empty(), "{:?}", unused[0].secondary());
}

#[test]
fn entirely_unused_variable_keeps_the_general_annotation() {
    let output = analyze("template T(){var dead=1;}");
    let unused = findings(&output, "CS0006");
    assert_eq!(unused.len(), 1);
    assert_eq!(unused[0].primary()[0].message, "This assigned value is unused.");
}

#[test]
fn unread_loop_variable_keeps_the_general_annotation() {
    let output = analyze("template T(){var dead=0;for(var i=0;i<2;i++){dead=1;}}");
    let unused = findings(&output, "CS0006");
    assert!(!unused.is_empty());
    assert!(unused
        .iter()
        .all(|report| report.primary()[0].message == "This assigned value is unused."));
}

#[test]
fn loop_update_read_after_the_loop_is_not_reported_as_unused() {
    let output = analyze(
        "template T(){var e2=1;var total=0;for(var i=0;i<2;i++){total+=e2;e2=e2+e2;}\
         signal output out;out<==total+e2;}",
    );
    assert!(findings(&output, "CS0006").iter().all(|report| !report.message().contains("e2")));
}

#[test]
fn conditional_uses_and_overwrites_keep_the_observed_argument_qualification() {
    for (body, value) in [
        ("var x=1;if(n){log(x);}", 0),
        ("var x=1;if(n){x++;}", 0),
        ("var x=1;if(n){x+=1;}", 0),
        ("var x=1;for(var i=0;i<n;i++){log(x);}", 0),
        ("var x=1;if(n){x=2;}log(x);", 1),
    ] {
        let output = analyze(&format!(
            "template Child(n){{{body}}}\
            template Main(){{component a=Child(0);component b=Child(1);}}component main=Main();"
        ));
        let unused = findings(&output, "CS0006");
        assert_eq!(unused.len(), 1, "{body}");
        let labels = unused[0].secondary();
        assert_eq!(labels.len(), 1, "{body}: {labels:?}");
        assert!(labels[0].message.contains(&format!("Child(n = {value})")), "{labels:?}");
        assert!(!labels[0].message.contains("context 1"));
        assert!(!labels[0].message.contains("Reached through"));
    }
}

#[test]
fn numeric_specialization_keeps_the_argument_that_produced_wraparound() {
    let output = analyze(
        "template Child(n){signal output out;out<==n-1;}\
        template Main(){component a=Child(0);component b=Child(1);}component main=Main();",
    );
    let arithmetic = findings(&output, "CS0004");
    assert_eq!(arithmetic.len(), 1);
    assert_eq!(arithmetic[0].secondary().len(), 1);
    assert!(arithmetic[0].secondary()[0].message.contains("Child(n = 0)"));
}

#[test]
fn a_later_parameter_is_not_hidden_by_argument_display_limits() {
    let output = analyze(
        "template Child(a,b,c,d,n){signal output out;out<==n-1;}\
        template Main(){component child=Child(1,2,3,4,0);}component main=Main();",
    );
    let arithmetic = findings(&output, "CS0004");
    assert_eq!(arithmetic.len(), 1);
    assert!(arithmetic[0].secondary()[0].message.contains("n = 0"));
}

#[test]
fn call_rhs_removability_keeps_its_specialization_context() {
    let output = analyze(
        "function Value(n){return n;}\
        template Child(n){var dead=Value(n);signal output out;out<==n;}\
        template Main(){component child=Child(1);}component main=Main();",
    );
    let removable = findings(&output, "CS0008");
    assert_eq!(removable.len(), 1);
    assert_eq!(removable[0].secondary().len(), 1);
    assert!(removable[0].secondary()[0].message.contains("Child(n = 1)"));
}
