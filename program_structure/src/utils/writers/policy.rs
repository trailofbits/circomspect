use std::collections::HashSet;

use crate::file_definition::FileID;
use crate::report::{MessageCategory, Report};
use crate::utils::writers::ReportFilter;

/// Select diagnostics by severity, primary source location and ignored IDs.
///
/// Source errors remain visible in included files. Level and ID filtering still apply to them.
#[derive(Clone)]
pub struct OutputPolicy {
    minimum: MessageCategory,
    inputs: HashSet<FileID>,
    ignored: HashSet<String>,
}

impl OutputPolicy {
    /// Create the shared terminal/SARIF policy for the given explicit input files.
    #[must_use]
    pub fn new(
        minimum: MessageCategory,
        inputs: HashSet<FileID>,
        ignored: HashSet<String>,
    ) -> Self {
        Self { minimum, inputs, ignored }
    }
}

impl ReportFilter for OutputPolicy {
    fn filter(&self, report: &Report) -> bool {
        if report.category() < &self.minimum {
            return false;
        }
        let files = report.primary_file_ids();
        let visible = *report.category() == MessageCategory::Error
            || files.is_empty()
            || files.iter().any(|file| self.inputs.contains(file));
        visible && !self.ignored.contains(&report.id())
    }
}
