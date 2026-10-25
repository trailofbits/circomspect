use std::path::Path;

use circomspect_program_analysis::new_rules::{Finding, RenderError, SourceMap};
use program_structure::report::{MessageCategory, Report};
use program_structure::writers::{OutputPolicy, ReportWriter, SarifWriter, StdoutWriter};

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
    Ok(render_reports(&reports, sources, minimum, allow, sarif_path))
}

/// Render parser and rule reports through both existing presentation paths.
pub fn render_reports(
    reports: &[Report],
    sources: &SourceMap<'_>,
    minimum: MessageCategory,
    allow: &[&str],
    sarif_path: &Path,
) -> (usize, usize) {
    let filter = OutputPolicy::new(
        minimum,
        sources.files().user_inputs().clone(),
        allow.iter().map(|id| (*id).to_string()).collect(),
    );
    let mut terminal = StdoutWriter::new(true).add_filter(filter.clone());
    let terminal_count =
        terminal.write_reports(reports, sources.files()).expect("terminal diagnostics");
    let mut sarif = SarifWriter::new(sarif_path).add_filter(filter);
    let sarif_count = sarif.write_reports(reports, sources.files()).expect("SARIF diagnostics");
    (terminal_count, sarif_count)
}
