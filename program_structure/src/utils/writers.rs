use std::fmt::Display;
use std::fs::File;
use std::io::{self, IsTerminal, Write};
use thiserror::Error;
use std::path::{PathBuf, Path};
use codespan_reporting::term;
use termcolor::{StandardStream, ColorChoice, WriteColor, ColorSpec, Color};

use crate::sarif_conversion::{SarifError, ToSarif};
use crate::{
    program_library::report::{Report, ReportCollection},
    file_definition::FileLibrary,
};

mod policy;

pub use crate::utils::writers::policy::OutputPolicy;

pub trait ReportFilter {
    /// Returns true if the report should be included.
    fn filter(&self, report: &Report) -> bool;
}

impl<F: Fn(&Report) -> bool> ReportFilter for F {
    fn filter(&self, report: &Report) -> bool {
        self(report)
    }
}

fn select_reports(filters: &[Box<dyn ReportFilter>], reports: &[Report]) -> ReportCollection {
    let mut selected = ReportCollection::new();
    for report in reports {
        if filters.iter().all(|filter| filter.filter(report)) {
            selected.push(report.clone());
        }
    }
    selected
}

/// A failure while rendering diagnostics or writing their output.
#[derive(Debug, Error)]
pub enum ReportWriteError {
    #[error("cannot write diagnostics to stdout: {0}")]
    Terminal(#[from] codespan_reporting::files::Error),
    #[error("cannot write status to stdout: {0}")]
    Status(#[from] io::Error),
    #[error("cannot serialize SARIF diagnostics: {0}")]
    Sarif(#[from] SarifError),
    #[error("cannot encode SARIF JSON: {0}")]
    Json(#[from] serde_json::Error),
    #[error("cannot write SARIF file {path}: {source}")]
    File { path: PathBuf, source: io::Error },
}

pub trait ReportWriter {
    /// Filter and write the given reports. Returns the number of reports written.
    ///
    /// # Errors
    /// Returns a rendering, serialization, or output error without discarding it.
    fn write_reports(
        &mut self,
        reports: &[Report],
        file_library: &FileLibrary,
    ) -> Result<usize, ReportWriteError>;

    /// Returns the number of reports written.
    #[must_use]
    fn reports_written(&self) -> usize;
}

pub trait LogWriter {
    /// Writes status messages in order.
    ///
    /// # Errors
    /// Returns the first failure writing to stdout.
    fn write_messages<D: Display>(&mut self, messages: &[D]) -> io::Result<()>;

    /// Writes one status message.
    ///
    /// # Errors
    /// Returns the output error if stdout cannot accept the message.
    fn write_message<D: Display>(&mut self, message: D) -> io::Result<()> {
        self.write_messages(&[message])
    }
}

pub struct StdoutWriter {
    verbose: bool,
    written: usize,
    writer: StandardStream,
    filters: Vec<Box<dyn ReportFilter>>,
}

impl StdoutWriter {
    #[must_use]
    pub fn new(verbose: bool) -> StdoutWriter {
        let writer = if std::io::stdout().is_terminal() {
            StandardStream::stdout(ColorChoice::Always)
        } else {
            StandardStream::stdout(ColorChoice::Never)
        };
        StdoutWriter { verbose, written: 0, writer, filters: Vec::new() }
    }

    #[must_use]
    pub fn add_filter(mut self, filter: impl ReportFilter + 'static) -> StdoutWriter {
        self.filters.push(Box::new(filter));
        self
    }
}

impl LogWriter for StdoutWriter {
    fn write_messages<D: Display>(&mut self, messages: &[D]) -> io::Result<()> {
        let mut spec = ColorSpec::new();
        spec.set_fg(Some(Color::Green));

        let write_impl = |message: &D| {
            let mut writer = self.writer.lock();
            writer.set_color(&spec)?;
            write!(&mut writer, "circomspect")?;
            writer.reset()?;
            writeln!(&mut writer, ": {message}")?;
            writer.flush()
        };
        for message in messages {
            write_impl(message)?;
        }
        Ok(())
    }
}

impl ReportWriter for StdoutWriter {
    fn write_reports(
        &mut self,
        reports: &[Report],
        file_library: &FileLibrary,
    ) -> Result<usize, ReportWriteError> {
        let reports = select_reports(&self.filters, reports);

        let mut config = term::Config::default();
        let mut diagnostics = Vec::new();
        let files = file_library.to_storage();
        for report in &reports {
            diagnostics.push(report.to_diagnostic(self.verbose));
        }
        config.styles.header_help.set_intense(false);
        config.styles.header_error.set_intense(false);
        config.styles.header_warning.set_intense(false);
        for diagnostic in &diagnostics {
            term::emit(&mut self.writer.lock(), &config, files, diagnostic)?;
            self.written += 1;
        }

        Ok(reports.len())
    }

    /// Returns the number of reports written.
    fn reports_written(&self) -> usize {
        self.written
    }
}

/// A `StdoutWriter` that caches all reports.
pub struct CachedStdoutWriter {
    writer: StdoutWriter,
    reports: ReportCollection,
}

impl CachedStdoutWriter {
    #[must_use]
    pub fn new(verbose: bool) -> CachedStdoutWriter {
        CachedStdoutWriter { writer: StdoutWriter::new(verbose), reports: ReportCollection::new() }
    }

    #[must_use]
    pub fn reports(&self) -> &ReportCollection {
        &self.reports
    }

    #[must_use]
    pub fn add_filter(mut self, filter: impl ReportFilter + 'static) -> CachedStdoutWriter {
        self.writer.filters.push(Box::new(filter));
        self
    }
}

impl LogWriter for CachedStdoutWriter {
    fn write_messages<D: Display>(&mut self, messages: &[D]) -> io::Result<()> {
        self.writer.write_messages(messages)
    }
}

impl ReportWriter for CachedStdoutWriter {
    fn write_reports(
        &mut self,
        reports: &[Report],
        file_library: &FileLibrary,
    ) -> Result<usize, ReportWriteError> {
        self.reports.extend(reports.iter().cloned());
        self.writer.write_reports(reports, file_library)
    }

    fn reports_written(&self) -> usize {
        self.writer.reports_written()
    }
}

#[derive(Default)]
pub struct SarifWriter {
    sarif_file: PathBuf,
    written: usize,
    filters: Vec<Box<dyn ReportFilter>>,
}

impl SarifWriter {
    #[must_use]
    pub fn new(sarif_file: &Path) -> SarifWriter {
        SarifWriter { sarif_file: sarif_file.to_owned(), ..Default::default() }
    }

    #[must_use]
    pub fn add_filter(mut self, filter: impl ReportFilter + 'static) -> SarifWriter {
        self.filters.push(Box::new(filter));
        self
    }

    fn serialize_reports(
        &self,
        reports: &ReportCollection,
        file_library: &FileLibrary,
    ) -> Result<(), ReportWriteError> {
        let sarif = reports.to_sarif(file_library)?;
        let json = serde_json::to_string_pretty(&sarif)?;
        let file_error = |source| ReportWriteError::File { path: self.sarif_file.clone(), source };
        let mut sarif_file = File::create(&self.sarif_file).map_err(file_error)?;
        writeln!(sarif_file, "{json}").map_err(file_error)?;
        Ok(())
    }
}

impl ReportWriter for SarifWriter {
    fn write_reports(
        &mut self,
        reports: &[Report],
        file_library: &FileLibrary,
    ) -> Result<usize, ReportWriteError> {
        let reports = select_reports(&self.filters, reports);
        self.serialize_reports(&reports, file_library)?;
        self.written += reports.len();
        Ok(reports.len())
    }

    fn reports_written(&self) -> usize {
        self.written
    }
}
