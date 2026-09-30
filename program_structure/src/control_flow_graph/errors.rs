use std::fmt::{Display, Formatter};

use crate::report_code::ReportCode;
use crate::report::Report;
use crate::file_definition::{FileID, FileLocation};
use crate::ir::errors::IRError;

/// Error enum for CFG generation errors.
#[derive(Debug)]
pub enum CFGError {
    UndefinedVariableError {
        name: String,
        file_id: Option<FileID>,
        file_location: FileLocation,
    },
    InvalidVariableNameError {
        name: String,
        file_id: Option<FileID>,
        file_location: FileLocation,
    },
    ShadowingVariableWarning {
        name: String,
        primary_file_id: Option<FileID>,
        primary_location: FileLocation,
        secondary_file_id: Option<FileID>,
        secondary_location: FileLocation,
    },
    ParameterNameCollisionError {
        name: String,
        file_id: Option<FileID>,
        file_location: FileLocation,
    },
}

impl Display for CFGError {
    fn fmt(&self, formatter: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UndefinedVariableError { name, .. } => {
                write!(formatter, "The variable `{name}` is read before it is declared/written.")
            }
            Self::InvalidVariableNameError { name, .. } => {
                write!(formatter, "The variable name `{name}` contains invalid characters.")
            }
            Self::ShadowingVariableWarning { name, .. } => write!(
                formatter,
                "The declaration of the variable `{name}` shadows a previous declaration."
            ),
            Self::ParameterNameCollisionError { name, .. } => write!(
                formatter,
                concat!(
                    "Multiple parameters with the same name `{}` ",
                    "in function or template definition."
                ),
                name
            ),
        }
    }
}

impl std::error::Error for CFGError {}

pub type CFGResult<T> = Result<T, CFGError>;

impl CFGError {
    pub fn into_report(self) -> Report {
        use CFGError::*;
        match self {
            UndefinedVariableError { name, file_id, file_location } => {
                let mut report = Report::error(
                    format!("The variable `{name}` is used before it is defined."),
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
            InvalidVariableNameError { name, file_id, file_location } => {
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
                report.add_note(format!("Consider renaming the second occurrence of `{name}`."));
                report
            }
            ParameterNameCollisionError { name, file_id, file_location } => {
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
            IRError::UndefinedVariableError { name, file_id, file_location } => {
                CFGError::UndefinedVariableError { name, file_id, file_location }
            }
            IRError::InvalidVariableNameError { name, file_id, file_location } => {
                CFGError::InvalidVariableNameError { name, file_id, file_location }
            }
        }
    }
}

impl From<CFGError> for Report {
    fn from(error: CFGError) -> Report {
        error.into_report()
    }
}
