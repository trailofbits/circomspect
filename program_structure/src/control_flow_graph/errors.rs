use thiserror::Error;

use crate::error_code::ReportCode;
use crate::error_definition::Report;
use crate::file_definition::{FileID, FileLocation};
use crate::ir::errors::IRError;

/// Error enum for CFG generation errors.
#[derive(Debug, Error)]
pub enum CFGError {
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
    #[error("The declaration or the variable `{name}` shadows a previous declaration.")]
    ShadowingVariableWarning {
        name: String,
        primary_file_id: Option<FileID>,
        primary_location: FileLocation,
        secondary_file_id: Option<FileID>,
        secondary_location: FileLocation,
    },
    #[error("Multiple parameters with the same name `{name}` in function or template definition.")]
    ParameterNameCollisionError {
        name: String,
        file_id: Option<FileID>,
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
                    format!("Variable `{name}` is used before it is defined."),
                    ReportCode::UninitializedSymbolInExpression,
                );
                if let Some(file_id) = file_id {
                    report.add_primary(
                        file_location,
                        file_id,
                        "Variable is first seen here.".to_string(),
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
            ShadowingVariableWarning {
                name,
                primary_file_id,
                primary_location,
                secondary_file_id,
                secondary_location,
            } => {
                let mut report = Report::warning(
                    format!("Declaration of variable `{name}` shadows previous declaration."),
                    ReportCode::ShadowingVariable,
                );
                if let Some(primary_file_id) = primary_file_id {
                    report.add_primary(
                        primary_location,
                        primary_file_id,
                        "Shadowing declaration here.".to_string(),
                    );
                }
                if let Some(secondary_file_id) = secondary_file_id {
                    report.add_secondary(
                        secondary_location,
                        secondary_file_id,
                        Some("Shadowed variable is declared here.".to_string()),
                    );
                }
                report.add_note(format!(
                    "Consider renaming the second occurrence of `{name}`."
                ));
                report
            }
            ParameterNameCollisionError {
                name,
                file_id,
                file_location,
            } => {
                let mut report = Report::warning(
                    format!("Parameter `{name}` declared multiple times."),
                    ReportCode::ParameterNameCollision,
                );
                if let Some(file_id) = file_id {
                    report.add_primary(
                        file_location,
                        file_id,
                        "Parameters declared here.".to_string(),
                    );
                }
                report.add_note(format!("Rename the second occurrence of `{name}`."));
                report
            }
        }
    }
}

impl From<IRError> for CFGError {
    fn from(error: IRError) -> CFGError {
        match error {
            IRError::UndefinedVariableError {
                name,
                file_id,
                file_location,
            } => CFGError::UndefinedVariableError {
                name,
                file_id,
                file_location,
            },
            IRError::InvalidVariableNameError {
                name,
                file_id,
                file_location,
            } => CFGError::InvalidVariableNameError {
                name,
                file_id,
                file_location,
            },
        }
    }
}

impl From<CFGError> for Report {
    fn from(error: CFGError) -> Report {
        CFGError::produce_report(error)
    }
}
