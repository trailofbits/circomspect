use std::collections::HashSet;
use std::num::NonZeroU64;
use std::time::Duration;

use crate::{analysis_timeout, AnalysisTimeout};

use program_structure::report::{MessageCategory, Report};
use program_structure::report_code::ReportCode;

use program_structure::writers::{OutputPolicy, ReportFilter};

struct SourceCase {
    name: &'static str,
    primary: &'static [usize],
    secondary: &'static [usize],
    visible: bool,
}

fn report(category: MessageCategory, primary: &[usize], secondary: &[usize]) -> Report {
    let mut report = match category {
        MessageCategory::Info => Report::info("finding".into(), ReportCode::ParseFail),
        MessageCategory::Warning => Report::warning("finding".into(), ReportCode::ParseFail),
        MessageCategory::Error => Report::error("finding".into(), ReportCode::ParseFail),
    };
    for file in primary {
        report.add_primary(0..1, *file, "primary".into());
    }
    for file in secondary {
        report.add_secondary(0..1, *file, Some("secondary".into()));
    }
    report
}

#[test]
fn source_visibility_uses_primary_locations_and_keeps_errors() {
    let cases = [
        SourceCase { name: "locationless", primary: &[], secondary: &[], visible: true },
        SourceCase { name: "input", primary: &[1], secondary: &[], visible: true },
        SourceCase { name: "include", primary: &[2], secondary: &[], visible: false },
        SourceCase { name: "multiple", primary: &[2, 1], secondary: &[], visible: true },
        SourceCase { name: "secondary only", primary: &[], secondary: &[1], visible: true },
        SourceCase { name: "input secondary", primary: &[2], secondary: &[1], visible: false },
    ];
    for case in cases {
        for category in [MessageCategory::Info, MessageCategory::Warning, MessageCategory::Error] {
            let report = report(category, case.primary, case.secondary);
            assert_eq!(
                OutputPolicy::new(MessageCategory::Info, HashSet::from([1]), HashSet::new())
                    .filter(&report),
                case.visible || category == MessageCategory::Error,
                "{} at {category}",
                case.name
            );
        }
    }
}

#[test]
fn minimum_level_keeps_only_categories_at_or_above_the_threshold() {
    let categories = [MessageCategory::Info, MessageCategory::Warning, MessageCategory::Error];
    let expected = [[true, true, true], [false, true, true], [false, false, true]];
    for (minimum, row) in categories.into_iter().zip(expected) {
        for (category, expected) in categories.into_iter().zip(row) {
            let policy = OutputPolicy::new(minimum, HashSet::new(), HashSet::new());
            assert_eq!(policy.filter(&report(category, &[], &[])), expected);
        }
    }
}

#[test]
fn allowed_ids_hide_errors_as_well_as_warnings_and_information() {
    for category in [MessageCategory::Info, MessageCategory::Warning, MessageCategory::Error] {
        let report = report(category, &[2], &[1]);
        for (ignored, expected) in [(vec!["P1000"], false), (vec!["CS0019"], true), (vec![], true)]
        {
            let policy = OutputPolicy::new(
                MessageCategory::Info,
                HashSet::from([2]),
                ignored.into_iter().map(str::to_owned).collect(),
            );
            assert_eq!(policy.filter(&report), expected);
        }
    }
}

#[test]
fn timeout_is_unlimited_by_default_and_bounded_when_requested() {
    assert_eq!(analysis_timeout(None), AnalysisTimeout::Unlimited);
    let seconds = NonZeroU64::new(3);
    assert_eq!(analysis_timeout(seconds), AnalysisTimeout::Bounded(Duration::from_secs(3)));
}
