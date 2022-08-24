use program_structure::abstract_syntax_tree::ast::Version;
use program_structure::error_code::ReportCode;
use program_structure::error_definition::Report;
use program_structure::file_definition::{FileID, FileLocation};

pub struct UnclosedCommentError {
    pub location: FileLocation,
    pub file_id: FileID,
}

impl UnclosedCommentError {
    pub fn produce_report(error: Self) -> Report {
        let mut report = Report::error(format!("unterminated /* */"), ReportCode::ParseFail);
        report.add_primary(
            error.location,
            error.file_id,
            format!("Comment starts here."),
        );
        report
    }
}

pub struct ParsingError {
    pub location: FileLocation,
    pub file_id: FileID,
    pub msg: String,
}

impl ParsingError {
    pub fn produce_report(error: Self) -> Report {
        let mut report = Report::error(error.msg, ReportCode::ParseFail);
        report.add_primary(error.location, error.file_id, format!("Invalid syntax"));
        report
    }
}

pub struct FileOsError {
    pub path: String,
}
impl FileOsError {
    pub fn into_report(self) -> Report {
        Report::error(
            format!("Failed to open file `{}`.", self.path),
            ReportCode::ParseFail,
        )
    }
}

pub struct MultipleMainError;
impl MultipleMainError {
    pub fn produce_report() -> Report {
        Report::error(
            format!("Multiple main components found in the project structure."),
            ReportCode::MultipleMainInComponent,
        )
    }
}

pub struct CompilerVersionError {
    pub path: String,
    pub required_version: Version,
    pub version: Version,
}
impl CompilerVersionError {
    pub fn produce_report(error: Self) -> Report {
        let message = format!(
            "File `{}` requires pragma version {}, which is not supported by circomspect (version {}).",
            error.path,
            version_string(&error.required_version),
            version_string(&error.version),
        );
        Report::error(message, ReportCode::CompilerVersionError)
    }
}

pub struct NoCompilerVersionWarning {
    pub path: String,
    pub version: Version,
}
impl NoCompilerVersionWarning {
    pub fn produce_report(error: Self) -> Report {
        Report::warning(
            format!(
                "File `{}` does not include pragma version. Assuming pragma version {}.",
                error.path,
                version_string(&error.version)
            ),
            ReportCode::NoCompilerVersionWarning,
        )
    }
}

fn version_string(version: &Version) -> String {
    format!("{}.{}.{}", version.0, version.1, version.2)
}
