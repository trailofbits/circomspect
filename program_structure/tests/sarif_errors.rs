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
