use log::debug;

use program_structure::cfg::Cfg;
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::*;

pub struct FieldElementComparisonWarning {
    file_id: FileID,
    file_location: FileLocation,
}

impl FieldElementComparisonWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::info(
            "Comparisons with field elements greater than `p/2` may produce unexpected results."
                .to_string(),
            ReportCode::FieldElementComparison,
        );
        report.add_primary(
            self.file_location,
            self.file_id,
            "Field element comparison here.".to_string(),
        );
        report.add_note(
            "Field elements `x` are always normalized as `x > p/2? x - p: x` before they are compared.".to_string()
        );
        report
    }
}

/// Field element comparisons in Circom may produce surprising results since
/// elements are normalized to the the half-open interval `(-p/2, p/2]` before
/// they are compared. In particular, this means that
///
///   - `p/2 < 0`,
///   - `p/2 + 1 < p/2 - 1`, and
///   - `2 * x < x` for any `p/4 < x < p/2`
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
        IfThenElse { cond, .. } => visit_expression(cond, reports),
        LogCall { arg, .. } => visit_expression(arg, reports),
        Assert { arg, .. } => visit_expression(arg, reports),
        ConstraintEquality { lhe, rhe, .. } => {
            visit_expression(lhe, reports);
            visit_expression(rhe, reports);
        }
        Return { .. } | Substitution { .. } => (),
    }
}

fn visit_expression(expr: &Expression, reports: &mut ReportCollection) {
    use Expression::*;
    match expr {
        InfixOp { meta, infix_op, .. } if is_comparison_op(infix_op) => {
            reports.push(build_report(meta));
        }
        InfixOp {
            infix_op, rhe, lhe, ..
        } if is_boolean_infix_op(infix_op) => {
            visit_expression(lhe, reports);
            visit_expression(rhe, reports);
        }
        PrefixOp { prefix_op, rhe, .. } if is_boolean_prefix_op(prefix_op) => {
            visit_expression(rhe, reports);
        }
        _ => (),
    }
}

fn is_comparison_op(op: &ExpressionInfixOpcode) -> bool {
    use ExpressionInfixOpcode::*;
    matches!(op, LesserEq | GreaterEq | Lesser | Greater)
}

fn is_boolean_infix_op(op: &ExpressionInfixOpcode) -> bool {
    use ExpressionInfixOpcode::*;
    matches!(op, BoolAnd | BoolOr)
}

fn is_boolean_prefix_op(op: &ExpressionPrefixOpcode) -> bool {
    use ExpressionPrefixOpcode::*;
    matches!(op, BoolNot)
}

fn build_report(meta: &Meta) -> Report {
    FieldElementComparisonWarning {
        file_id: meta.get_file_id(),
        file_location: meta.file_location(),
    }
    .into_report()
}
