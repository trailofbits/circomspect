use log::debug;

use program_structure::cfg::Cfg;
use program_structure::report_code::ReportCode;
use program_structure::report::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::*;

pub struct FieldElementComparisonWarning {
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl FieldElementComparisonWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::info(
            "Comparisons with field elements greater than `p/2` may produce unexpected results."
                .to_string(),
            ReportCode::FieldElementComparison,
        );
        if let Some(file_id) = self.file_id {
            report.add_primary(
                self.file_location,
                file_id,
                "Field element comparison here.".to_string(),
            );
        }
        report.add_note(
            "Field elements are always normalized to the interval `(-p/2, p/2]` before they are compared.".to_string()
        );
        report
    }
}

/// Field element comparisons in Circom may produce surprising results since
/// elements are normalized to the the half-open interval `(-p/2, p/2]` before
/// they are compared. In particular, this means that the statements
///
///   1. `p/2 + 1 < 0`,
///   2. `p/2 + 1 < p/2 - 1`, and
///   3. `2 * x < x` for any `p/4 < x < p/2`
///
/// are all true.
pub fn find_field_element_comparisons(cfg: &Cfg) -> ReportCollection {
    debug!("running field element comparison analysis pass");
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
    match stmt {
        Declaration { dimensions, .. } => {
            for size in dimensions {
                visit_expression(size, reports);
            }
        }
        IfThenElse { cond, .. } => visit_expression(cond, reports),
        Substitution { rhe, .. } => visit_expression(rhe, reports),
        Return { value, .. } => visit_expression(value, reports),
        LogCall { arg, .. } => visit_expression(arg, reports),
        Assert { arg, .. } => visit_expression(arg, reports),
        ConstraintEquality { lhe, rhe, .. } => {
            visit_expression(lhe, reports);
            visit_expression(rhe, reports);
        }
    }
}

fn visit_expression(expr: &Expression, reports: &mut ReportCollection) {
    use Expression::*;
    match expr {
        InfixOp { meta, infix_op, .. } if is_comparison_op(infix_op) => {
            reports.push(build_report(meta));
        }
        InfixOp { lhe, rhe, .. } => {
            visit_expression(lhe, reports);
            visit_expression(rhe, reports);
        }
        PrefixOp { rhe, .. } => {
            visit_expression(rhe, reports);
        }
        SwitchOp { cond, if_true, if_false, .. } => {
            visit_expression(cond, reports);
            visit_expression(if_true, reports);
            visit_expression(if_false, reports);
        }
        Call { args, .. } => {
            for arg in args {
                visit_expression(arg, reports);
            }
        }
        Array { values, .. } => {
            for value in values {
                visit_expression(value, reports);
            }
        }
        Access { access, .. } => {
            for index in access {
                if let AccessType::ArrayAccess(index) = index {
                    visit_expression(index, reports);
                }
            }
        }
        Update { access, rhe, .. } => {
            for index in access {
                if let AccessType::ArrayAccess(index) = index {
                    visit_expression(index, reports);
                }
            }
            visit_expression(rhe, reports);
        }
        Number(_, _) | Variable { .. } | Phi { .. } => (),
    }
}

fn is_comparison_op(op: &ExpressionInfixOpcode) -> bool {
    use ExpressionInfixOpcode::*;
    matches!(op, LesserEq | GreaterEq | Lesser | Greater)
}

fn build_report(meta: &Meta) -> Report {
    FieldElementComparisonWarning { file_id: meta.file_id(), file_location: meta.file_location() }
        .into_report()
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::cfg::IntoCfg;

    use super::*;

    #[test]
    fn test_field_comparisons() {
        let src = r#"
            function f(a) {
                var b = a + 1;
                while (a > 0) {
                    a -= 1;
                }
                if (b < a + 2) {
                    a += 1;
                }
                var c = a + b + 1;
                return (a < b) && (b < c);
            }
        "#;
        validate_reports(src, 4);
    }

    fn validate_reports(src: &str, expected_len: usize) {
        // Build CFG.
        let mut reports = ReportCollection::new();
        let cfg =
            parse_definition(src).unwrap().into_cfg(&mut reports).unwrap().into_ssa().unwrap();
        assert!(reports.is_empty());

        // Generate report collection.
        let reports = find_field_element_comparisons(&cfg);

        assert_eq!(reports.len(), expected_len);
    }
}
