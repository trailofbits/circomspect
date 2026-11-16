// Fixture setup and assertions intentionally fail the test on errors.
#![allow(clippy::allow_attributes, clippy::expect_used, clippy::unwrap_used)]

use std::io;
use std::path::PathBuf;
use std::time::Duration;

use circomspect_program_analysis::application::{
    analyze_files, analyze_files_with_observer, AnalysisObserver, AnalysisOutput, AnalysisProgress,
    ApplicationError,
};
use circomspect_program_analysis::application::AnalysisTimeout;
use program_structure::constants::Curve;
use program_structure::file_definition::FileLibrary;
use program_structure::report::{Report, ReportLabel};
use program_structure::sarif_conversion::ToSarif;
use program_structure::writers::ReportWriteError;

struct Fixture(PathBuf);

impl Fixture {
    fn new(source: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "circomspect-stream-{}-{:?}.circom",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::write(&path, format!("pragma circom 2.2.3;\n{source}")).unwrap();
        Self(path)
    }

    fn analyze(
        &self,
        observer: &mut dyn AnalysisObserver,
    ) -> Result<AnalysisOutput, ApplicationError> {
        analyze_files_with_observer(
            std::slice::from_ref(&self.0),
            &[],
            Curve::Bn254,
            circomspect_program_analysis::application::AnalysisTimeout::Unlimited,
            observer,
        )
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        std::fs::remove_file(&self.0).unwrap();
    }
}

#[derive(Default)]
struct Recorder {
    events: Vec<String>,
    reports: Vec<Report>,
    paths: Vec<(Report, Vec<ReportLabel>)>,
    fail: Option<&'static str>,
}

impl AnalysisObserver for Recorder {
    fn progress(&mut self, progress: AnalysisProgress<'_>) -> io::Result<()> {
        self.events.push(format!("{progress:?}"));
        Ok(())
    }

    fn report(&mut self, report: &Report, _files: &FileLibrary) -> Result<(), ReportWriteError> {
        self.events.push(report.id());
        if self.fail == Some(report.id().as_str()) {
            return Err(ReportWriteError::Status(io::Error::from_raw_os_error(28)));
        }
        self.reports.push(report.clone());
        Ok(())
    }

    fn additional_call_paths(
        &mut self,
        report: &Report,
        locations: &[ReportLabel],
        _files: &FileLibrary,
    ) -> Result<(), ReportWriteError> {
        if self.fail == Some("paths") {
            return Err(ReportWriteError::Status(io::Error::from_raw_os_error(28)));
        }
        self.paths.push((report.clone(), locations.to_vec()));
        Ok(())
    }
}

fn reports(output: &AnalysisOutput) -> serde_json::Value {
    let mut reports = output.diagnostics.clone();
    for scope in &output.scopes {
        reports.extend(scope.reports.iter().cloned());
    }
    serde_json::to_value(reports.to_sarif(&output.files).unwrap()).unwrap()
}

const LIBRARY: &str = "template Broken(){component c=Missing();}\n\
    template Early(){var dead=7;signal output out;out<==0;}\n\
    template Later(){signal output out;out<==1;}";

#[test]
fn missing_include_has_a_sentence_cased_source_annotation() {
    let fixture = Fixture::new("include \"missing.circom\"; template T(){}");
    let output = analyze_files(std::slice::from_ref(&fixture.0), &[], Curve::Bn254).unwrap();
    let report = output.diagnostics.iter().find(|report| report.id() == "P1000").unwrap();
    assert_eq!(report.primary()[0].message, "This include cannot be resolved.");
}

#[test]
fn per_context_timeout_reports_incomplete_scopes_and_continues() {
    let fixture = Fixture::new("template First(){} template Second(){}");
    let mut observer = Recorder::default();
    let output = analyze_files_with_observer(
        std::slice::from_ref(&fixture.0),
        &[],
        Curve::Bn254,
        AnalysisTimeout::Bounded(Duration::ZERO),
        &mut observer,
    )
    .unwrap();
    assert_eq!(output.diagnostics.iter().filter(|report| report.id() == "T3002").count(), 2);
    assert!(observer.events.iter().any(|event| event.contains("First")));
    assert!(observer.events.iter().any(|event| event.contains("Second")));
    assert!(output.scopes.iter().all(|scope| scope.reports.is_empty()));
    assert_eq!(observer.reports.iter().filter(|report| report.id() == "T3002").count(), 2);
    let warnings: Vec<_> =
        output.diagnostics.iter().filter(|report| report.id() == "T3002").collect();
    assert!(warnings
        .iter()
        .all(|report| report.primary().is_empty() && report.secondary().is_empty()));
    assert!(warnings.iter().any(|report| {
        report.message() == "Analysis of the 'First' template timed out after 0 seconds."
    }));
    assert!(warnings.iter().any(|report| {
        report.message() == "Analysis of the 'Second' template timed out after 0 seconds."
    }));
    let sarif = reports(&output);
    assert_eq!(sarif["runs"][0]["results"].as_array().unwrap().len(), 2);
}

#[test]
fn diagnostics_arrive_before_independent_analysis_finishes() {
    let fixture = Fixture::new(LIBRARY);
    let mut observer = Recorder::default();
    let observed = fixture.analyze(&mut observer).unwrap();
    let position = |name: &str| observer.events.iter().position(|event| event == name).unwrap();
    assert!(position("CS0019") < position("IndexingProject"));
    assert!(position("CS0006") < position("AnalyzingTemplate(\"Later\")"));
    let quiet = analyze_files(std::slice::from_ref(&fixture.0), &[], Curve::Bn254).unwrap();
    assert_eq!(reports(&quiet), reports(&observed));
}

const CALLERS: &str = "template Child(n){var dead=1;signal output out;out<==n;}\n\
    template Main(){component a=Child(1);component b=Child(2);}\n\
    component main=Main();";

#[test]
fn repeated_source_findings_stream_once_without_irrelevant_context_notes() {
    let fixture = Fixture::new(CALLERS);
    let mut observer = Recorder::default();
    let output = fixture.analyze(&mut observer).unwrap();
    let unused: Vec<_> = observer.reports.iter().filter(|report| report.id() == "CS0006").collect();
    assert_eq!(unused.len(), 1);
    let extensions: Vec<_> =
        observer.paths.iter().filter(|(report, _)| report.id() == "CS0006").collect();
    assert!(extensions.is_empty());
    let final_reports = reports(&output);
    let final_unused: Vec<_> = final_reports["runs"][0]["results"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|report| report["ruleId"] == "CS0006")
        .collect();
    assert_eq!(final_unused.len(), 1);
    assert!(final_unused[0]["relatedLocations"].as_array().map_or(true, Vec::is_empty));
}

#[test]
fn errors_discovered_from_call_arguments_arrive_before_later_scopes() {
    let fixture = Fixture::new(
        "template Child(n){var x=n;x=1;signal output out;out<==1;}\n\
        template Parent(){component c=Child([1,2]);}\n\
        template Later(){signal output out;out<==1;}\n\
        component main=Parent();",
    );
    let mut observer = Recorder::default();
    fixture.analyze(&mut observer).unwrap();
    let position = |name: &str| observer.events.iter().position(|event| event == name).unwrap();
    assert!(position("AnalyzingTemplate(\"Child\")") < position("T2000"));
    assert!(position("T2000") < position("AnalyzingTemplate(\"Later\")"));
    assert_eq!(observer.reports.iter().filter(|report| report.id() == "T2000").count(), 1);
}

#[test]
fn included_definition_findings_do_not_leak_through_streaming_or_finalization() {
    let fixture = Fixture::new("");
    let dependency = fixture.0.with_extension("included.circom");
    std::fs::write(
        &dependency,
        "pragma circom 2.2.3;template Child(n){var dead=1;signal output out;out<==n;}",
    )
    .unwrap();
    std::fs::write(
        &fixture.0,
        format!(
            "pragma circom 2.2.3;include \"{}\";\n\
        template Main(){{component a=Child(1);component b=Child(2);}}\n\
        component main=Main();",
            dependency.display(),
        ),
    )
    .unwrap();
    let mut observer = Recorder::default();
    let output = fixture.analyze(&mut observer).unwrap();
    std::fs::remove_file(dependency).unwrap();
    assert!(observer.reports.iter().all(|report| report.id() != "CS0006"));
    assert!(observer.paths.iter().all(|(report, _)| report.id() != "CS0006"));
    assert!(output
        .scopes
        .iter()
        .flat_map(|scope| &scope.reports)
        .all(|report| report.id() != "CS0006"));
}

#[test]
fn diagnostic_and_continuation_failures_stop_analysis_without_becoming_findings() {
    let specialized = "template Child(n){var x=1;if(n==1){log(x);}}\
        template Main(){component a=Child(0);component b=Child(-1);}component main=Main();";
    for (source, fail) in [(LIBRARY, "CS0019"), (LIBRARY, "CS0006"), (specialized, "paths")] {
        let fixture = Fixture::new(source);
        let mut observer = Recorder { fail: Some(fail), ..Recorder::default() };
        let error = fixture.analyze(&mut observer).err().expect("output failure must propagate");
        let ApplicationError::Output(ReportWriteError::Status(error)) = error else {
            unreachable!("the original observer error must be preserved");
        };
        assert_eq!(error.raw_os_error(), Some(28));
        assert!(!observer.events.iter().any(|event| event == "AnalyzingTemplate(\"Later\")"));
    }
}
