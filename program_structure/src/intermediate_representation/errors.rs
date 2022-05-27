use crate::error_code::ReportCode;
use crate::error_definition::Report;
use crate::file_definition::{FileID, FileLocation};

/// Error enum for IR generation errors.
pub enum IRError {
    /// The variable is read before it is declared/written.
    UndefinedVariableError {
        name: String,
        file_id: Option<FileID>,
        file_location: FileLocation,
    },
}

pub type IRResult<T> = Result<T, IRError>;

impl IRError {
    pub fn produce_report(error: Self) -> Report {
        use IRError::*;
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
                if let Some(file_id) = file_id {
                    report.add_primary(
                        file_location,
                        file_id,
                        "variable is first seen here".to_string(),
                    );
                }
                report
            }
        }
    }
}

impl Into<Report> for IRError {
    fn into(self) -> Report {
        IRError::produce_report(self)
    }
}
