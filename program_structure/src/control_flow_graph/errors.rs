use crate::error_code::ReportCode;
use crate::error_definition::Report;
use crate::file_definition::{FileID, FileLocation};

/// Error enum for CFG generation errors.
pub enum CFGError {
    /// The variable is read before it is declared/written.
    UndefinedVariableError {
        name: String,
        file_id: FileID,
        file_location: FileLocation,
    },
    /// The variable declaration shadows a previous declaration.
    ShadowingVariableWarning {
        name: String,
        primary_file_id: FileID,
        primary_location: FileLocation,
        secondary_file_id: FileID,
        secondary_location: FileLocation,
    },
    /// Multiple parameters with the same name in function or template definition.
    ParameterNameCollisionError {
        name: String,
        file_id: FileID,
        file_location: FileLocation,
    },
}

pub type CFGResult<T> = Result<T, CFGError>;

impl CFGError {
    pub fn produce_report(error: Self) -> Report {
        use CFGError::*;
        match error {
            UndefinedVariableError {
                name,
                file_id,
                file_location,
            } => {
                let mut report = Report::error(
                    format!("variable '{name}' is used before it is defined"),
                    ReportCode::UninitializedSymbolInExpression,
                );
                report.add_primary(file_location, file_id, "variable is first seen here".to_string());
                report
            }
            ShadowingVariableWarning { name, primary_file_id, primary_location, secondary_file_id, secondary_location } => {
                let mut report = Report::warning(
                format!("declaration of variable '{name}' shadows previous declaration"),
                ReportCode::ShadowingVariable,
                );
                report.add_primary(
                    primary_location,
                    primary_file_id,
                    "shadowing declaration here".to_string(),
                );
                report.add_secondary(
                    secondary_location,
                    secondary_file_id,
                    Some("shadowed variable is declared here".to_string()),
                );
                report.add_note(format!("consider renaming the second occurrence of '{name}'"));
                report
            }
            ParameterNameCollisionError { name, file_id, file_location } => {
                let mut report = Report::warning(
                    format!("parameter '{name}' declared multiple times"),
                    ReportCode::ParameterNameCollision,
                );
                report.add_primary(
                    file_location,
                    file_id,
                    "parameters declared here".to_string(),
                );
                report.add_note(format!("rename the second occurrence of '{name}'"));
                report
            }
        }
    }
}

impl Into<Report> for CFGError {
    fn into(self) -> Report {
        CFGError::produce_report(self)
    }
}
