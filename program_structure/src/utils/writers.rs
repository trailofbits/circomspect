use anyhow;
use anyhow::Context;
use log::{info, warn};
use std::fmt::Display;
use std::fs::File;
use std::io::Write;
use std::path::{PathBuf, Path};
use codespan_reporting::term;
use termcolor::{StandardStream, ColorChoice, WriteColor, ColorSpec, Color};

use crate::sarif_conversion::ToSarif;
use crate::{
    program_library::report::{Report, ReportCollection},
    file_definition::FileLibrary,
};

pub trait ReportFilter {
    /// Returns true if the report should be included.
    fn filter(&self, report: &Report) -> bool;
}

impl<F: Fn(&Report) -> bool> ReportFilter for F {
    fn filter(&self, report: &Report) -> bool {
        self(report)
    }
}

pub trait ReportWriter {
    /// Filter and write the given reports. Returns the number of reports written.
    fn write_reports(&mut self, reports: &[Report], file_library: &FileLibrary) -> usize;

    /// Filter and write a single report. Returns the number of reports written (0 or 1).
    fn write_report(&mut self, report: Report, file_library: &FileLibrary) -> usize {
        self.write_reports(&[report], file_library)
    }

    /// Returns the number of reports written.
    #[must_use]
    fn reports_written(&self) -> usize;
}

pub trait LogWriter {
    fn write_messages<D: Display>(&mut self, messages: &[D]);

    fn write_message<D: Display>(&mut self, message: D) {
        self.write_messages(&[message]);
    }
}

pub struct StdoutWriter {
    verbose: bool,
    written: usize,
    writer: StandardStream,
    filters: Vec<Box<dyn ReportFilter>>,
}

impl StdoutWriter {
    pub fn new(verbose: bool) -> StdoutWriter {
        let writer = if atty::is(atty::Stream::Stdout) {
            StandardStream::stdout(ColorChoice::Always)
        } else {
            StandardStream::stdout(ColorChoice::Never)
        };
        StdoutWriter { verbose, written: 0, writer, filters: Vec::new() }
    }

    pub fn add_filter(mut self, filter: impl ReportFilter + 'static) -> StdoutWriter {
        self.filters.push(Box::new(filter));
        self
    }

    fn filter(&self, reports: &[Report]) -> ReportCollection {
        reports
            .iter()
            .filter(|report| self.filters.iter().all(|f| f.filter(report)))
            .cloned()
            .collect()
    }
}

impl LogWriter for StdoutWriter {
    fn write_messages<D: Display>(&mut self, messages: &[D]) {
        let mut spec = ColorSpec::new();
        spec.set_fg(Some(Color::Green));

        let write_impl = |message: &D| {
            let mut writer = self.writer.lock();
            writer.set_color(&spec)?;
            write!(&mut writer, "circomspect")?;
            writer.reset()?;
            writeln!(&mut writer, ": {message}")
        };
        for message in messages {
            write_impl(message).expect("failed to write log messages")
        }
    }
}

impl ReportWriter for StdoutWriter {
    fn write_reports(&mut self, reports: &[Report], file_library: &FileLibrary) -> usize {
        let reports = self.filter(reports);

        let mut config = term::Config::default();
        let mut diagnostics = Vec::new();
        let files = file_library.to_storage();
        for report in reports.iter() {
            diagnostics.push(report.to_diagnostic(self.verbose));
        }
        config.styles.header_help.set_intense(false);
        config.styles.header_error.set_intense(false);
        config.styles.header_warning.set_intense(false);
        for diagnostic in diagnostics.iter() {
            term::emit(&mut self.writer.lock(), &config, files, diagnostic)
                .expect("failed to write reports");
        }

        self.written += reports.len();
        reports.len()
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
    pub fn new(verbose: bool) -> CachedStdoutWriter {
        CachedStdoutWriter { writer: StdoutWriter::new(verbose), reports: ReportCollection::new() }
    }

    pub fn reports(&self) -> &ReportCollection {
        &self.reports
    }

    pub fn add_filter(mut self, filter: impl ReportFilter + 'static) -> CachedStdoutWriter {
        self.writer.filters.push(Box::new(filter));
        self
    }
}

impl LogWriter for CachedStdoutWriter {
    fn write_messages<D: Display>(&mut self, messages: &[D]) {
        self.writer.write_messages(messages)
    }
}

impl ReportWriter for CachedStdoutWriter {
    fn write_reports(&mut self, reports: &[Report], file_library: &FileLibrary) -> usize {
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
    pub fn new(sarif_file: &Path) -> SarifWriter {
        SarifWriter { sarif_file: sarif_file.to_owned(), ..Default::default() }
    }

    pub fn add_filter(mut self, filter: impl ReportFilter + 'static) -> SarifWriter {
        self.filters.push(Box::new(filter));
        self
    }

    fn filter(&self, reports: &[Report]) -> ReportCollection {
        reports
            .iter()
            .filter(|report| self.filters.iter().all(|f| f.filter(report)))
            .cloned()
            .collect()
    }

    fn serialize_reports(
        &self,
        reports: &ReportCollection,
        file_library: &FileLibrary,
    ) -> anyhow::Result<()> {
        let sarif =
            reports.to_sarif(file_library).context("failed to convert reports to Sarif format")?;
        let json = serde_json::to_string_pretty(&sarif)?;
        let mut sarif_file = File::create(&self.sarif_file)?;
        writeln!(sarif_file, "{}", &json)
            .with_context(|| format!("could not write to {}", self.sarif_file.display()))?;
        Ok(())
    }
}

impl ReportWriter for SarifWriter {
    fn write_reports(&mut self, reports: &[Report], file_library: &FileLibrary) -> usize {
        let reports = self.filter(reports);
        match self.serialize_reports(&reports, file_library) {
            Ok(()) => {
                info!("reports written to `{}`", self.sarif_file.display());
                self.written += reports.len();
                reports.len()
            }
            Err(_) => {
                warn!("failed to write reports to `{}`", self.sarif_file.display());
                0
            }
        }
    }

    fn reports_written(&self) -> usize {
        self.written
    }
}
