use crate::report_code::ReportCode;
use crate::report::Report;
use crate::file_definition::{FileID, FileLocation};

/// Error enum for SSA generation errors.
#[derive(Debug)]
pub enum SSAError {
    /// The variable is read before it is declared/written.
    UndefinedVariableError { name: String, file_id: Option<FileID>, location: FileLocation },
}

pub type SSAResult<T> = Result<T, SSAError>;

impl SSAError {
    pub fn into_report(&self) -> Report {
        use SSAError::*;
        match self {
            UndefinedVariableError { name, file_id, location } => {
                let mut report = Report::error(
                    format!("The variable `{name}` is used before it is defined."),
                    ReportCode::UninitializedSymbolInExpression,
                );
                if let Some(file_id) = file_id {
                    report.add_primary(
                        location.clone(),
                        *file_id,
                        format!("The variable `{name}` is first seen here."),
                    );
                }
                report
            }
        }
    }
}

impl From<SSAError> for Report {
    fn from(error: SSAError) -> Report {
        error.into_report()
    }
}
