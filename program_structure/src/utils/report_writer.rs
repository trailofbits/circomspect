use anyhow;
use anyhow::Context;
use log::{info, warn};
use std::fs::File;
use std::io::Write;
use std::path::{PathBuf, Path};

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
    fn write(&mut self, reports: &ReportCollection, file_library: &FileLibrary) -> usize;

    /// Returns the number of reports written.
    #[must_use]
    fn written(&self) -> usize;
}

#[derive(Default)]
pub struct StdoutWriter {
    verbose: bool,
    written: usize,
    filters: Vec<Box<dyn ReportFilter>>,
}

impl StdoutWriter {
    pub fn new(verbose: bool) -> StdoutWriter {
        StdoutWriter { verbose, ..Default::default() }
    }

    pub fn add_filter(mut self, filter: impl ReportFilter + 'static) -> StdoutWriter {
        self.filters.push(Box::new(filter));
        self
    }

    fn filter(&self, reports: &ReportCollection) -> ReportCollection {
        reports
            .iter()
            .filter(|report| self.filters.iter().all(|f| f.filter(report)))
            .cloned()
            .collect()
    }
}

impl ReportWriter for StdoutWriter {
    fn write(&mut self, reports: &ReportCollection, file_library: &FileLibrary) -> usize {
        let reports = self.filter(reports);
        Report::print_reports(&reports, file_library, self.verbose);
        self.written += reports.len();
        reports.len()
    }

    /// Returns the number of reports written.
    fn written(&self) -> usize {
        self.written
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

    fn filter(&self, reports: &ReportCollection) -> ReportCollection {
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
    fn write(&mut self, reports: &ReportCollection, file_library: &FileLibrary) -> usize {
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

    fn written(&self) -> usize {
        self.written
    }
}
