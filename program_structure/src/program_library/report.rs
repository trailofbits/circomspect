use anyhow::anyhow;
use std::cmp::Ordering;
use std::fmt::Display;
use std::str::FromStr;

use codespan_reporting::diagnostic::{Diagnostic, Label};

use super::report_code::ReportCode;
use super::file_definition::{FileID, FileLocation};

pub type ReportCollection = Vec<Report>;
pub type DiagnosticCode = String;
pub type ReportLabel = Label<FileID>;
type ReportNote = String;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum MessageCategory {
    Error,
    Warning,
    Info,
}

/// Message categories are linearly ordered.
impl PartialOrd for MessageCategory {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for MessageCategory {
    fn cmp(&self, other: &Self) -> Ordering {
        use MessageCategory::*;
        match (self, other) {
            // `Info <= _`
            (Info, Info) => Ordering::Equal,
            (Info, Warning) | (Info, Error) => Ordering::Less,
            // `Warning <= _`
            (Warning, Warning) => Ordering::Equal,
            (Warning, Error) => Ordering::Less,
            // `Error <= _`
            (Error, Error) => Ordering::Equal,
            // All other cases are on the form `_ >= _`.
            _ => Ordering::Greater,
        }
    }
}

impl Display for MessageCategory {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use MessageCategory::*;
        match self {
            Error => write!(f, "error"),
            Warning => write!(f, "warning"),
            Info => write!(f, "info"),
        }
    }
}

impl FromStr for MessageCategory {
    type Err = anyhow::Error;

    fn from_str(category: &str) -> Result<MessageCategory, Self::Err> {
        match category.to_lowercase().as_str() {
            "warning" => Ok(MessageCategory::Warning),
            "info" => Ok(MessageCategory::Info),
            "error" => Ok(MessageCategory::Error),
            _ => Err(anyhow!("unknown level '{category}'")),
        }
    }
}

impl MessageCategory {
    /// Convert message category to Sarif level.
    pub fn to_level(&self) -> String {
        use MessageCategory::*;
        match self {
            Error => "error",
            Warning => "warning",
            Info => "note",
        }
        .to_string()
    }
}

#[derive(Clone)]
pub struct Report {
    category: MessageCategory,
    message: String,
    primary_file_ids: Vec<FileID>,
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
            primary_file_ids: Vec::new(),
            primary: Vec::new(),
            secondary: Vec::new(),
            notes: Vec::new(),
            code,
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
        self.primary_mut().push(label);
        self.primary_file_ids_mut().push(file_id);
        self
    }

    pub fn add_secondary(
        &mut self,
        location: FileLocation,
        file_id: FileID,
        possible_message: Option<String>,
    ) -> &mut Self {
        let mut label = ReportLabel::secondary(file_id, location);
        if let Some(message) = possible_message {
            label = label.with_message(message);
        }
        self.secondary_mut().push(label);
        self
    }

    pub fn add_note(&mut self, note: String) -> &mut Self {
        self.notes_mut().push(note);
        self
    }

    pub fn to_diagnostic(&self, verbose: bool) -> Diagnostic<FileID> {
        let mut labels = self.primary().clone();
        let mut secondary = self.secondary().clone();
        labels.append(&mut secondary);

        let diagnostic = match self.category() {
            MessageCategory::Error => Diagnostic::error(),
            MessageCategory::Warning => Diagnostic::warning(),
            MessageCategory::Info => Diagnostic::note(),
        }
        .with_message(self.message())
        .with_labels(labels);

        let mut notes = self.notes().clone();
        if let Some(url) = self.code().url() {
            // Add URL to documentation if available.
            notes.push(format!("For more details, see {url}."));
        }
        if verbose {
            // Add report code and note on `--allow ID`.
            notes.push(format!("To ignore this type of result, use `--allow {}`.", self.id()));
            diagnostic.with_code(self.id()).with_notes(notes)
        } else {
            diagnostic.with_notes(notes)
        }
    }

    pub fn primary_file_ids(&self) -> &Vec<FileID> {
        &self.primary_file_ids
    }

    fn primary_file_ids_mut(&mut self) -> &mut Vec<FileID> {
        &mut self.primary_file_ids
    }

    pub fn category(&self) -> &MessageCategory {
        &self.category
    }

    pub fn message(&self) -> &String {
        &self.message
    }

    pub fn primary(&self) -> &Vec<ReportLabel> {
        &self.primary
    }

    fn primary_mut(&mut self) -> &mut Vec<ReportLabel> {
        &mut self.primary
    }

    pub fn secondary(&self) -> &Vec<ReportLabel> {
        &self.secondary
    }

    fn secondary_mut(&mut self) -> &mut Vec<ReportLabel> {
        &mut self.secondary
    }

    pub fn notes(&self) -> &Vec<ReportNote> {
        &self.notes
    }

    fn notes_mut(&mut self) -> &mut Vec<ReportNote> {
        &mut self.notes
    }

    pub fn code(&self) -> &ReportCode {
        &self.code
    }

    pub fn id(&self) -> String {
        self.code.id()
    }

    pub fn name(&self) -> String {
        self.code.name()
    }
}
