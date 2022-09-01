use thiserror::Error;

use crate::error_code::ReportCode;
use crate::error_definition::Report;
use crate::file_definition::{FileID, FileLocation};

/// Error enum for IR generation errors.
#[derive(Debug, Error)]
pub enum IRError {
    #[error("The variable `{name}` is read before it is declared/written.")]
    UndefinedVariableError {
        name: String,
        file_id: Option<FileID>,
        file_location: FileLocation,
    },
    #[error("The variable name `{name}` contains invalid characters.")]
    InvalidVariableNameError {
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
                    format!("The variable '{name}' is used before it is defined."),
                    ReportCode::UninitializedSymbolInExpression,
                );
                if let Some(file_id) = file_id {
                    report.add_primary(
                        file_location,
                        file_id,
                        format!("The variable `{name}` is first seen here."),
                    );
                }
                report
            }
            InvalidVariableNameError {
                name,
                file_id,
                file_location,
            } => {
                let mut report = Report::error(
                    format!("Invalid variable name `{name}`."),
                    ReportCode::ParseFail,
                );
                if let Some(file_id) = file_id {
                    report.add_primary(
                        file_location,
                        file_id,
                        "This variable name contains invalid characters.".to_string(),
                    );
                }
                report
            }
        }
    }
}

impl From<IRError> for Report {
    fn from(error: IRError) -> Report {
        IRError::produce_report(error)
    }
}
