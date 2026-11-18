// Assertions and fixture setup intentionally fail the test on errors.
#![allow(clippy::allow_attributes, clippy::expect_used, clippy::unwrap_used)]

use std::io;
use std::path::PathBuf;

use circomspect_program_analysis::application::{
    analyze_files, analyze_files_with_progress, AnalysisOutput, AnalysisProgress, ApplicationError,
};
use program_structure::constants::Curve;
use program_structure::sarif_conversion::ToSarif;

fn fixture() -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-observer-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join("library.circom");
    std::fs::write(
        &path,
        "pragma circom 2.2.3; function identity(x){return x;} \
         template Library(){signal output out;out<--identity(1);}",
    )
    .unwrap();
    path
}

fn reports(output: &AnalysisOutput) -> serde_json::Value {
    let mut reports = output.diagnostics.clone();
    for scope in &output.scopes {
        reports.extend(scope.reports.iter().cloned());
    }
    serde_json::to_value(reports.to_sarif(&output.files).unwrap()).unwrap()
}

#[test]
fn progress_preserves_reports_and_visits_each_analyzed_context() {
    let path = fixture();
    let paths = [path.clone()];
    let quiet = analyze_files(&paths, &[], Curve::Bn254).unwrap();
    let mut events = Vec::new();
    let observed = analyze_files_with_progress(&paths, &[], Curve::Bn254, |event| {
        events.push(format!("{event:?}"));
        Ok(())
    })
    .unwrap();
    assert_eq!(reports(&quiet), reports(&observed));
    assert_eq!(
        events,
        [
            "LoadingSources",
            "LiftingSources",
            "IndexingProject",
            "AnalyzingFunction(\"identity\")",
            "AnalyzingTemplate(\"Library\")",
            "AnalyzingFunction(\"identity\")",
        ]
    );
    std::fs::remove_file(path).unwrap();
}

#[test]
fn failed_progress_write_stops_at_each_stage() {
    let path = fixture();
    for stop in 0..6 {
        let mut count = 0;
        let result = analyze_files_with_progress(
            std::slice::from_ref(&path),
            &[],
            Curve::Bn254,
            |_: AnalysisProgress<'_>| {
                let current = count;
                count += 1;
                if current == stop {
                    Err(io::Error::new(io::ErrorKind::BrokenPipe, "observer closed"))
                } else {
                    Ok(())
                }
            },
        );
        let error = result.err().expect("the progress failure must stop analysis");
        let ApplicationError::Progress(error) = error else {
            unreachable!("progress errors must not become source diagnostics");
        };
        assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
        assert_eq!(error.to_string(), "observer closed");
        assert_eq!(count, stop + 1);
    }
    std::fs::remove_file(path).unwrap();
}
