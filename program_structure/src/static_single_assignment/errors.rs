use crate::error_code::ReportCode;
use crate::error_definition::Report;
use crate::file_definition::{FileID, FileLocation};

/// Error enum for SSA generation errors.
#[derive(Debug)]
pub enum SSAError {
    /// The variable is read before it is declared/written.
    UndefinedVariableError {
        name: String,
        file_id: Option<FileID>,
        location: FileLocation,
    },
}

pub type SSAResult<T> = Result<T, SSAError>;

impl SSAError {
    pub fn produce_report(error: Self) -> Report {
        use SSAError::*;
        match error {
            UndefinedVariableError {
                name,
                file_id,
                location,
            } => {
                let mut report = Report::error(
                    format!("The variable `{name}` is used before it is defined."),
                    ReportCode::UninitializedSymbolInExpression,
                );
                if let Some(file_id) = file_id {
                    report.add_primary(
                        location,
                        file_id,
                        format!("The variable `{name}` is first seen here."),
                    );
                }
                report
            }
        }
    }
}

impl Into<Report> for SSAError {
    fn into(self) -> Report {
        SSAError::produce_report(self)
    }
}
