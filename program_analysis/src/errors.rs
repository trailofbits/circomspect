use program_structure::error_code::ReportCode;
use program_structure::error_definition::Report;
use program_structure::file_definition::{FileID, FileLocation};

pub struct ShadowedVariableWarning {
    pub name: String,
    pub primary_file_id: FileID,
    pub primary_location: FileLocation,
    pub secondary_file_id: FileID,
    pub secondary_location: FileLocation,
}

impl ShadowedVariableWarning {
    pub fn produce_report(error: Self) -> Report {
        let mut report = Report::warning(
            format!(
                "Declaration of variable '{}' shadows previous declaration",
                error.name
            ),
            ReportCode::ShadowedVariable,
        );
        report.add_primary(
            error.primary_location,
            error.primary_file_id,
            "shadowing declaration here".to_string(),
        );
        report.add_secondary(
            error.secondary_location,
            error.secondary_file_id,
            Some("shadowed variable is declared here".to_string()),
        );
        report.add_note(format!(
            "Consider renaming the second occurence of '{}'",
            error.name
        ));
        report
    }
}
