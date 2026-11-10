use std::cell::OnceCell;
use std::collections::HashSet;
use std::io;

use program_analysis::application::{AnalysisObserver, AnalysisProgress};
use program_structure::file_definition::FileLibrary;
use program_structure::report::{MessageCategory, Report, ReportLabel};
use program_structure::writers::{
    OutputPolicy, ReportFilter, ReportWriteError, ReportWriter, StdoutWriter,
};

use crate::progress::ProgressReporter;

#[cfg(test)]
mod tests;

pub(super) struct LiveOutput<'a> {
    progress: &'a ProgressReporter,
    writer: &'a mut StdoutWriter,
    minimum: MessageCategory,
    ignored: &'a HashSet<String>,
    policy: OnceCell<OutputPolicy>,
}

impl<'a> LiveOutput<'a> {
    pub(super) fn new(
        progress: &'a ProgressReporter,
        writer: &'a mut StdoutWriter,
        minimum: MessageCategory,
        ignored: &'a HashSet<String>,
    ) -> Self {
        Self { progress, writer, minimum, ignored, policy: OnceCell::new() }
    }

    fn visible(&self, report: &Report, files: &FileLibrary) -> bool {
        self.policy
            .get_or_init(|| {
                OutputPolicy::new(self.minimum, files.user_inputs().clone(), self.ignored.clone())
            })
            .filter(report)
    }
}

impl AnalysisObserver for LiveOutput<'_> {
    fn progress(&mut self, progress: AnalysisProgress<'_>) -> io::Result<()> {
        self.progress.stage(progress)
    }

    fn report(&mut self, report: &Report, files: &FileLibrary) -> Result<(), ReportWriteError> {
        if self.visible(report, files) {
            self.writer.write_reports(std::slice::from_ref(report), files)?;
        }
        Ok(())
    }

    fn additional_call_paths(
        &mut self,
        report: &Report,
        locations: &[ReportLabel],
        files: &FileLibrary,
    ) -> Result<(), ReportWriteError> {
        if self.visible(report, files) {
            self.writer.write_additional_call_paths(report, locations, files)?;
        }
        Ok(())
    }
}
