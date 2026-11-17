// Test fixtures deliberately use temporary files and fail on setup errors.
#![allow(clippy::allow_attributes, clippy::expect_used, clippy::unwrap_used)]

use std::path::PathBuf;

use circomspect_program_analysis::application::analyze_files;
use program_structure::constants::Curve;
use program_structure::report::Report;
use program_structure::sarif_conversion::ToSarif;

struct Fixture(PathBuf);

impl Fixture {
    fn new(name: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "circomspect-unit-compat-{name}-{}-{:?}",
            std::process::id(),
            std::thread::current().id(),
        ));
        std::fs::create_dir_all(&path).unwrap();
        Self(path.canonicalize().unwrap())
    }

    fn write(&self, name: &str, source: &str) -> PathBuf {
        let path = self.0.join(name);
        std::fs::write(&path, source).unwrap();
        path
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

fn all_reports(output: &circomspect_program_analysis::application::AnalysisOutput) -> Vec<Report> {
    let mut reports = output.diagnostics.clone();
    for scope in &output.scopes {
        reports.extend(scope.reports.iter().cloned());
    }
    reports
}

#[test]
fn independent_mains_reuse_names_without_duplicate_errors() {
    let fixture = Fixture::new("same-template");
    fixture.write(
        "first.circom",
        "pragma circom 2.2.3; template Shared(){signal output out;out<==1;} \
         component main=Shared();",
    );
    fixture.write(
        "second.circom",
        "pragma circom 2.2.3; template Shared(){signal output out;out<==2;} \
         component main=Shared();",
    );
    let output = analyze_files(std::slice::from_ref(&fixture.0), &[], Curve::Bn254).unwrap();
    let reports = all_reports(&output);
    assert!(!reports
        .iter()
        .any(|report| { ["T2006", "T2007", "P1002"].contains(&report.id().as_str()) }));
    assert_eq!(
        output.scopes.iter().filter(|scope| scope.description == "template 'Shared'").count(),
        2
    );
}

#[test]
fn one_include_closure_still_reports_duplicate_definitions() {
    let fixture = Fixture::new("real-duplicate");
    fixture.write("a.circom", "pragma circom 2.2.3; template Shared(){}");
    fixture.write("b.circom", "pragma circom 2.2.3; template Shared(){}");
    let entry = fixture.write(
        "entry.circom",
        "pragma circom 2.2.3; include \"a.circom\"; include \"b.circom\"; \
         component main=Shared();",
    );
    let output = analyze_files(&[entry], &[], Curve::Bn254).unwrap();
    assert!(all_reports(&output).iter().any(|report| report.id() == "T2007"));
}

#[test]
fn reports_from_separate_roots_retain_sarif_file_locations() {
    let fixture = Fixture::new("sarif-locations");
    let first = fixture.write("first.circom", "pragma circom 2.2.3; template A(){var unused=1;}");
    let second = fixture.write("second.circom", "pragma circom 2.2.3; template B(){var unused=2;}");
    let output = analyze_files(&[first.clone(), second.clone()], &[], Curve::Bn254).unwrap();
    let reports = all_reports(&output);
    let sarif = serde_json::to_value(reports.to_sarif(&output.files).unwrap()).unwrap();
    let results = sarif["runs"][0]["results"].as_array().unwrap();
    let locations: Vec<_> = results
        .iter()
        .flat_map(|result| result["locations"].as_array().into_iter().flatten())
        .filter_map(|location| location["physicalLocation"]["artifactLocation"]["uri"].as_str())
        .collect();
    assert!(locations.iter().any(|uri| uri.ends_with(first.to_str().unwrap())));
    assert!(locations.iter().any(|uri| uri.ends_with(second.to_str().unwrap())));
}

#[test]
fn mainless_library_does_not_claim_an_enclosing_call_is_missing() {
    let fixture = Fixture::new("orphan-helper");
    let helper = fixture
        .write("helper.circom", "pragma circom 2.2.3; function Helper(){return Enclosing();}");
    for input in [fixture.0.clone(), helper] {
        let output = analyze_files(&[input], &[], Curve::Bn254).unwrap();
        let reports = all_reports(&output);
        assert!(!reports.iter().any(|report| report.id() == "CS0019"));
        assert!(reports.iter().any(|report| report.id() == "CS0020"));
    }
}

#[test]
fn included_helper_resolves_against_its_main() {
    let fixture = Fixture::new("included-helper");
    fixture.write("helper.circom", "function Helper(){return Enclosing();}");
    fixture.write(
        "main.circom",
        "pragma circom 2.2.3; include \"helper.circom\"; \
         function Enclosing(){return 1;} template Main(){signal output out;out<==Helper();} \
         component main=Main();",
    );
    let output = analyze_files(std::slice::from_ref(&fixture.0), &[], Curve::Bn254).unwrap();
    assert!(!all_reports(&output).iter().any(|report| report.id() == "CS0019"));
}

#[test]
fn missing_call_in_main_remains_a_source_error() {
    let fixture = Fixture::new("missing-in-main");
    let entry = fixture.write(
        "main.circom",
        "pragma circom 2.2.3; template Main(){component c=Missing();} component main=Main();",
    );
    let output = analyze_files(&[entry], &[], Curve::Bn254).unwrap();
    assert!(all_reports(&output).iter().any(|report| report.id() == "CS0019"));
}
