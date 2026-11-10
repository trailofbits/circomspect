use std::io;

use program_structure::file_definition::FileLibrary;
use program_structure::report::{Report, ReportLabel};
use program_structure::writers::ReportWriteError;

use crate::application::AnalysisProgress;

/// Receives progress and diagnostics synchronously while analysis runs.
///
/// Each source issue is reported once. Later callers can extend its provenance
/// through `additional_call_paths`; aggregate coverage notices arrive at completion.
/// The returned `AnalysisOutput` retains the complete reports in source order.
pub trait AnalysisObserver {
    /// Announce work before it starts.
    ///
    /// # Errors
    /// Return an output error to stop analysis before beginning this stage.
    fn progress(&mut self, _progress: AnalysisProgress<'_>) -> io::Result<()> {
        Ok(())
    }

    /// Publish a new diagnostic with all evidence currently available.
    ///
    /// # Errors
    /// Return a rendering or output error to stop analysis immediately.
    fn report(&mut self, _report: &Report, _files: &FileLibrary) -> Result<(), ReportWriteError> {
        Ok(())
    }

    /// Attach the complete final useful call context to an already published diagnostic.
    ///
    /// These locations extend the earlier report; they are not another finding.
    /// Filter using the original report's severity, code and primary locations.
    ///
    /// # Errors
    /// Return a rendering or output error to stop finalization immediately.
    fn additional_call_paths(
        &mut self,
        _report: &Report,
        _locations: &[ReportLabel],
        _files: &FileLibrary,
    ) -> Result<(), ReportWriteError> {
        Ok(())
    }
}

impl<F: FnMut(AnalysisProgress<'_>) -> io::Result<()>> AnalysisObserver for F {
    fn progress(&mut self, progress: AnalysisProgress<'_>) -> io::Result<()> {
        self(progress)
    }
}
