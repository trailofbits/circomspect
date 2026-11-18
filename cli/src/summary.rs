use program_structure::report::{MessageCategory, Report};
use program_structure::report_code::ReportCode;
use program_structure::writers::ReportFilter;

pub(super) fn describe(reports: &[Report], policy: &impl ReportFilter) -> String {
    let mut source_errors = 0;
    let mut project_errors = 0;
    let mut findings = 0;
    let mut notes = 0;
    let mut limits = 0;
    let mut analysis_errors = 0;
    let timeouts = timeout_count(reports);
    for report in reports {
        if let ReportCode::AnalysisTimeout = report.code() {
            continue;
        }
        if !policy.filter(report) {
            continue;
        }
        if let ReportCode::ProjectSetup = report.code() {
            project_errors += 1;
        } else if let ReportCode::RuntimeError = report.code() {
            analysis_errors += 1;
        } else if let ReportCode::IncompleteCoverage = report.code() {
            match report.category() {
                MessageCategory::Info => notes += 1,
                MessageCategory::Warning => limits += 1,
                MessageCategory::Error => analysis_errors += 1,
            }
        } else if report.category() == &MessageCategory::Error {
            source_errors += 1;
        } else {
            findings += 1;
        }
    }
    let mut parts = Vec::new();
    append_count(&mut parts, source_errors, "source error", "source errors");
    append_count(&mut parts, project_errors, "project setup error", "project setup errors");
    append_count(&mut parts, findings, "finding", "findings");
    if source_errors == 0 && project_errors == 0 && findings == 0 && analysis_errors == 0 {
        parts.push("No findings reported.".into());
    }
    append_count(&mut parts, notes, "analysis note", "analysis notes");
    append_count(&mut parts, limits, "analysis limitation", "analysis limitations");
    append_count(&mut parts, analysis_errors, "analyzer error", "analyzer errors");
    if timeouts > 0 {
        let noun = if timeouts == 1 { "analysis" } else { "analyses" };
        parts.push(format!("{timeouts} {noun} timed out."));
    }
    parts.join(" ")
}

pub(super) fn timeout_count(reports: &[Report]) -> usize {
    reports.iter().filter(|report| *report.code() == ReportCode::AnalysisTimeout).count()
}

fn append_count(parts: &mut Vec<String>, count: usize, singular: &str, plural: &str) {
    if count > 0 {
        let label = if count == 1 { singular } else { plural };
        parts.push(format!("{count} {label} reported."));
    }
}

#[cfg(test)]
mod tests {
    use program_structure::report::{MessageCategory, Report};
    use program_structure::report_code::ReportCode;

    use crate::summary::describe;

    #[test]
    fn summaries_separate_findings_errors_and_visible_analysis_notes() {
        let reports = [
            Report::error("missing include".into(), ReportCode::ParseFail),
            Report::warning("unused value".into(), ReportCode::UnusedVariableValue),
            Report::info("unknown parameter".into(), ReportCode::IncompleteCoverage),
            Report::warning("unsupported bus".into(), ReportCode::IncompleteCoverage),
            Report::error("internal failure".into(), ReportCode::RuntimeError),
        ];
        assert_eq!(
            describe(&reports, &|_: &Report| true),
            "1 source error reported. 1 finding reported. 1 analysis note reported. \
             1 analysis limitation reported. 1 analyzer error reported."
        );
        let visible = |report: &Report| report.category() >= &MessageCategory::Warning;
        assert!(!describe(&reports, &visible).contains("analysis note"));
    }

    #[test]
    fn hidden_context_notes_leave_no_summary_or_issue_count() {
        let reports = [Report::info("unknown parameter".into(), ReportCode::IncompleteCoverage)];
        assert_eq!(describe(&reports, &|_: &Report| false), "No findings reported.");
        assert_eq!(
            describe(&reports, &|_: &Report| true),
            "No findings reported. 1 analysis note reported."
        );
    }

    #[test]
    fn project_setup_failure_is_separate_from_source_errors() {
        let reports = [Report::error("missing package".into(), ReportCode::ProjectSetup)];
        assert_eq!(describe(&reports, &|_: &Report| true), "1 project setup error reported.");
    }

    #[test]
    fn findings_without_errors_or_timeouts_have_a_short_summary() {
        let reports = [Report::warning("unused value".into(), ReportCode::UnusedVariableValue)];
        assert_eq!(describe(&reports, &|_: &Report| true), "1 finding reported.");
        assert_eq!(describe(&[], &|_: &Report| true), "No findings reported.");
    }

    #[test]
    fn timeout_warnings_have_their_own_count() {
        let reports = [
            Report::error("bad include".into(), ReportCode::ParseFail),
            Report::warning("unused value".into(), ReportCode::UnusedVariableValue),
            Report::warning("slow scope".into(), ReportCode::AnalysisTimeout),
            Report::warning("another slow scope".into(), ReportCode::AnalysisTimeout),
        ];
        assert_eq!(
            describe(&reports, &|_: &Report| true),
            "1 source error reported. 1 finding reported. 2 analyses timed out."
        );
        assert_eq!(
            describe(&reports, &|_: &Report| false),
            "No findings reported. 2 analyses timed out."
        );
    }
}
