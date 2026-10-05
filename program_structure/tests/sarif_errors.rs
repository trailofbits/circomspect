// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use circomspect_program_structure::file_definition::FileLibrary;
use circomspect_program_structure::report::Report;
use circomspect_program_structure::report_code::ReportCode;
use circomspect_program_structure::sarif_conversion::{SarifError, ToSarif};

#[test]
fn relative_source_path_has_an_actionable_serialization_error() {
    let mut files = FileLibrary::new();
    let file = files.add_file("relative.circom".into(), "x".into(), true);
    let mut report = Report::error("invalid source".into(), ReportCode::ParseFail);
    report.add_primary(0..1, file, "invalid token".into());
    let error = report.to_sarif(&files).unwrap_err();
    assert!(error.to_string().contains("relative.circom"));
    assert!(error.to_string().contains("absolute file URI"));
    let SarifError::InvalidFilePath(path) = error else { panic!("expected file path error") };
    assert_eq!(path.to_str(), Some("relative.circom"));
}

#[test]
fn reversed_source_range_returns_an_actionable_error() {
    let mut files = FileLibrary::new();
    let file = files.add_file("/source.circom".into(), "token".into(), true);
    let mut report = Report::error("invalid source".into(), ReportCode::ParseFail);
    report.add_primary(std::ops::Range { start: 4, end: 1 }, file, "invalid token".into());
    let error = report.to_sarif(&files).unwrap_err();
    assert!(error.to_string().contains("4..1"), "{error}");
}

#[test]
fn failed_sarif_write_preserves_the_error_and_does_not_count_reports() {
    use circomspect_program_structure::writers::{ReportWriteError, ReportWriter, SarifWriter};

    let directory = std::env::temp_dir();
    let mut writer = SarifWriter::new(&directory);
    let report = Report::error("a finding".into(), ReportCode::ParseFail);
    let error = writer.write_reports(&[report], &FileLibrary::new()).unwrap_err();
    let ReportWriteError::File { path, .. } = error else { panic!("expected file error") };
    assert_eq!(path, directory);
    assert_eq!(writer.reports_written(), 0);
}
