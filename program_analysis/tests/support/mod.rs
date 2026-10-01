use std::collections::HashSet;
use std::path::Path;

use circomspect_program_analysis::new_rules::{Finding, RenderError, SourceMap};
use program_structure::file_definition::FileID;
use program_structure::report::{MessageCategory, Report};
use program_structure::writers::{ReportFilter, ReportWriter, SarifWriter, StdoutWriter};

#[derive(Clone)]
struct Filter {
    minimum: MessageCategory,
    roots: HashSet<FileID>,
    allow: HashSet<String>,
}

impl ReportFilter for Filter {
    fn filter(&self, report: &Report) -> bool {
        let visible_source = *report.category() == MessageCategory::Error
            || report.primary_file_ids().is_empty()
            || report.primary_file_ids().iter().any(|id| self.roots.contains(id));
        visible_source && report.category() >= &self.minimum && !self.allow.contains(&report.id())
    }
}

/// Exercise the same terminal and SARIF renderers with the CLI's report filters.
pub fn render(
    findings: &[Finding],
    sources: &SourceMap<'_>,
    minimum: MessageCategory,
    allow: &[&str],
    sarif_path: &Path,
) -> Result<(usize, usize), RenderError> {
    let reports =
        findings.iter().map(|finding| finding.to_report(sources)).collect::<Result<Vec<_>, _>>()?;
    let filter = Filter {
        minimum,
        roots: sources.files().user_inputs().clone(),
        allow: allow.iter().map(|id| (*id).to_string()).collect(),
    };
    let mut terminal = StdoutWriter::new(true).add_filter(filter.clone());
    let terminal_count = terminal.write_reports(&reports, sources.files());
    let mut sarif = SarifWriter::new(sarif_path).add_filter(filter);
    let sarif_count = sarif.write_reports(&reports, sources.files());
    Ok((terminal_count, sarif_count))
}
