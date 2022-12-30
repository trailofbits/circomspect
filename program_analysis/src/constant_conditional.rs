use log::debug;

use program_structure::cfg::Cfg;
use program_structure::report_code::ReportCode;
use program_structure::report::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::value_meta::ValueReduction;
use program_structure::ir::*;

pub struct ConstantBranchConditionWarning {
    value: bool,
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl ConstantBranchConditionWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            "Constant branching statement condition found.".to_string(),
            ReportCode::ConstantBranchCondition,
        );
        if let Some(file_id) = self.file_id {
            report.add_primary(
                self.file_location,
                file_id,
                format!("This condition is always {}.", self.value),
            );
        }
        report
    }
}

/// This analysis pass uses basic constant propagation to determine cases where
/// an if-statement condition is always true or false.
pub fn find_constant_conditional_statement(cfg: &Cfg) -> ReportCollection {
    debug!("running constant conditional analysis pass");
    let mut reports = ReportCollection::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            visit_statement(stmt, &mut reports);
        }
    }
    debug!("{} new reports generated", reports.len());
    reports
}

fn visit_statement(stmt: &Statement, reports: &mut ReportCollection) {
    use Statement::*;
    use ValueReduction::*;
    if let IfThenElse { cond, .. } = stmt {
        let value = cond.meta().value_knowledge();
        if let Boolean(Some(value)) = dbg!(value) {
            reports.push(build_report(cond.meta(), *value));
        }
    }
}

fn build_report(meta: &Meta, value: bool) -> Report {
    ConstantBranchConditionWarning {
        value,
        file_id: meta.file_id(),
        file_location: meta.file_location(),
    }
    .into_report()
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::{cfg::IntoCfg, constants::Curve};

    use super::*;

    #[test]
    fn test_constant_conditional() {
        let src = r#"
            function f(x) {
                var a = 1;
                var b = (2 * a * a + 1) << 2;
                var c = (3 * b / b - 2) >> 1;
                if (c > 4) {
                    a += x;
                    b += x * a;
                }
                return a + b;
            }
        "#;
        validate_reports(src, 1);

        let src = r#"
            function f(x) {
                var a = 1;
                var b = (2 * a * a + 1) << 2;
                var c = (3 * b / x - 2) >> 1;
                if (c > 4) {
                    a += x;
                    b += x * a;
                }
                return a + b;
            }
        "#;
        validate_reports(src, 0);
    }

    fn validate_reports(src: &str, expected_len: usize) {
        // Build CFG.
        let mut reports = ReportCollection::new();
        let cfg = parse_definition(src)
            .unwrap()
            .into_cfg(&Curve::default(), &mut reports)
            .unwrap()
            .into_ssa()
            .unwrap();
        assert!(reports.is_empty());

        // Generate report collection.
        let reports = find_constant_conditional_statement(&cfg);

        assert_eq!(reports.len(), expected_len);
    }
}
