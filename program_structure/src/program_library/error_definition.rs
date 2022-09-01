use super::error_code::ReportCode;
use super::file_definition::{FileID, FileLibrary, FileLocation};
use atty;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::term;

pub type ReportCollection = Vec<Report>;
pub type DiagnosticCode = String;
pub type ReportLabel = Label<FileID>;
type ReportNote = String;

#[derive(Copy, Clone)]
pub enum MessageCategory {
    Error,
    Warning,
    Info,
}

impl ToString for MessageCategory {
    fn to_string(&self) -> String {
        use MessageCategory::*;
        match self {
            Error => "error",
            Warning => "warning",
            Info => "info",
        }
        .to_string()
    }
}

#[derive(Clone)]
pub struct Report {
    category: MessageCategory,
    message: String,
    primary: Vec<ReportLabel>,
    secondary: Vec<ReportLabel>,
    notes: Vec<ReportNote>,
    code: ReportCode,
}

impl Report {
    fn new(category: MessageCategory, message: String, code: ReportCode) -> Report {
        Report {
            category,
            message,
            primary: Vec::new(),
            secondary: Vec::new(),
            notes: Vec::new(),
            code,
        }
    }

    pub fn print_reports(reports: &[Report], file_library: &FileLibrary) {
        use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
        let writer = if atty::is(atty::Stream::Stdout) {
            StandardStream::stdout(ColorChoice::Always)
        } else {
            StandardStream::stdout(ColorChoice::Never)
        };
        let mut config = term::Config::default();
        let mut diagnostics = Vec::new();
        let files = file_library.to_storage();
        for report in reports.iter() {
            diagnostics.push(report.to_diagnostic());
        }
        config.styles.header_help.set_intense(false);
        config.styles.header_error.set_intense(false);
        config.styles.header_warning.set_intense(false);
        for diagnostic in diagnostics.iter() {
            let print_result = term::emit(&mut writer.lock(), &config, files, diagnostic);
            if print_result.is_err() {
                panic!("error printing reports")
            }
        }
    }

    pub fn error(message: String, code: ReportCode) -> Report {
        Report::new(MessageCategory::Error, message, code)
    }

    pub fn warning(message: String, code: ReportCode) -> Report {
        Report::new(MessageCategory::Warning, message, code)
    }

    pub fn info(message: String, code: ReportCode) -> Report {
        Report::new(MessageCategory::Info, message, code)
    }

    pub fn add_primary(
        &mut self,
        location: FileLocation,
        file_id: FileID,
        message: String,
    ) -> &mut Self {
        let label = ReportLabel::primary(file_id, location).with_message(message);
        self.get_mut_primary().push(label);
        self
    }

    pub fn add_secondary(
        &mut self,
        location: FileLocation,
        file_id: FileID,
        possible_message: Option<String>,
    ) -> &mut Self {
        let mut label = ReportLabel::secondary(file_id, location);
        if let Option::Some(message) = possible_message {
            label = label.with_message(message);
        }
        self.get_mut_secondary().push(label);
        self
    }

    pub fn add_note(&mut self, note: String) -> &mut Self {
        self.get_mut_notes().push(note);
        self
    }

    fn to_diagnostic(&self) -> Diagnostic<FileID> {
        let mut labels = self.get_primary().clone();
        let mut secondary = self.get_secondary().clone();
        labels.append(&mut secondary);

        match self.get_category() {
            MessageCategory::Error => Diagnostic::error(),
            MessageCategory::Warning => Diagnostic::warning(),
            MessageCategory::Info => Diagnostic::note(),
        }
        .with_message(self.get_message())
        .with_labels(labels)
        .with_notes(self.get_notes().clone())
    }

    pub fn get_category(&self) -> &MessageCategory {
        &self.category
    }

    pub fn get_message(&self) -> &String {
        &self.message
    }

    pub fn get_primary(&self) -> &Vec<ReportLabel> {
        &self.primary
    }

    fn get_mut_primary(&mut self) -> &mut Vec<ReportLabel> {
        &mut self.primary
    }

    pub fn get_secondary(&self) -> &Vec<ReportLabel> {
        &self.secondary
    }

    fn get_mut_secondary(&mut self) -> &mut Vec<ReportLabel> {
        &mut self.secondary
    }

    pub fn get_notes(&self) -> &Vec<ReportNote> {
        &self.notes
    }

    fn get_mut_notes(&mut self) -> &mut Vec<ReportNote> {
        &mut self.notes
    }

    pub fn get_code(&self) -> &ReportCode {
        &self.code
    }
}
