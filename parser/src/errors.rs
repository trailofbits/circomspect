use program_structure::ast::{Meta, Version};
use program_structure::report_code::ReportCode;
use program_structure::report::Report;
use program_structure::file_definition::{FileID, FileLocation};

pub struct UnclosedCommentError {
    pub location: FileLocation,
    pub file_id: FileID,
}

impl UnclosedCommentError {
    pub fn into_report(self) -> Report {
        let mut report = Report::error("Unterminated comment.".to_string(), ReportCode::ParseFail);
        report.add_primary(self.location, self.file_id, "Comment starts here.".to_string());
        report
    }
}

pub struct ParsingError {
    pub location: FileLocation,
    pub file_id: FileID,
    pub message: String,
}

impl ParsingError {
    pub fn into_report(self) -> Report {
        let mut report = Report::error(self.message, ReportCode::ParseFail);
        report.add_primary(
            self.location,
            self.file_id,
            "This token is invalid or unexpected here.".to_string(),
        );
        report
    }
}

pub struct FileOsError {
    pub path: String,
}
impl FileOsError {
    pub fn into_report(self) -> Report {
        Report::error(format!("Failed to open file `{}`.", self.path), ReportCode::ParseFail)
    }
}

pub struct IncludeError {
    pub path: String,
    pub file_id: Option<FileID>,
    pub file_location: FileLocation,
}
impl IncludeError {
    pub fn into_report(self) -> Report {
        let mut report =
            Report::error(format!("Failed to open file `{}`.", self.path), ReportCode::ParseFail);
        if let Some(file_id) = self.file_id {
            report.add_primary(self.file_location, file_id, "File included here.".to_string());
        }
        report
    }
}

pub struct MultipleMainError;
impl MultipleMainError {
    pub fn produce_report() -> Report {
        Report::error(
            "Multiple main components found in the project structure.".to_string(),
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
    pub fn into_report(self) -> Report {
        let message = format!(
            "The file `{}` requires version {}, which is not supported by Circomspect (version {}).",
            self.path,
            version_string(&self.required_version),
            version_string(&self.version),
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
                "The file `{}` does not include a version pragma. Assuming version {}.",
                error.path,
                version_string(&error.version)
            ),
            ReportCode::NoCompilerVersionWarning,
        )
    }
}

pub struct AnonymousComponentError {
    pub meta: Option<Meta>,
    pub message: String,
    pub primary: Option<String>,
}

impl AnonymousComponentError {
    pub fn new(meta: Option<&Meta>, message: &str, primary: Option<&str>) -> Self {
        AnonymousComponentError {
            meta: meta.cloned(),
            message: message.to_string(),
            primary: primary.map(ToString::to_string),
        }
    }

    pub fn into_report(self) -> Report {
        let mut report = Report::error(self.message, ReportCode::AnonymousComponentError);
        if let Some(meta) = self.meta {
            let primary = self.primary.unwrap_or_else(|| "The problem occurs here.".to_string());
            report.add_primary(meta.file_location(), meta.get_file_id(), primary);
        }
        report
    }

    pub fn boxed_report(meta: &Meta, message: &str) -> Box<Report> {
        Box::new(Self::new(Some(meta), message, None).into_report())
    }
}

pub struct TupleError {
    pub meta: Option<Meta>,
    pub message: String,
    pub primary: Option<String>,
}

impl TupleError {
    pub fn new(meta: Option<&Meta>, message: &str, primary: Option<&str>) -> Self {
        TupleError {
            meta: meta.cloned(),
            message: message.to_string(),
            primary: primary.map(ToString::to_string),
        }
    }

    pub fn into_report(self) -> Report {
        let mut report = Report::error(self.message, ReportCode::TupleError);
        if let Some(meta) = self.meta {
            let primary = self.primary.unwrap_or_else(|| "The problem occurs here.".to_string());
            report.add_primary(meta.file_location(), meta.get_file_id(), primary);
        }
        report
    }

    pub fn boxed_report(meta: &Meta, message: &str) -> Box<Report> {
        Box::new(Self::new(Some(meta), message, None).into_report())
    }
}

fn version_string(version: &Version) -> String {
    format!("{}.{}.{}", version.0, version.1, version.2)
}
