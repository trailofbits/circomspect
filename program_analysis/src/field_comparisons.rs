use program_structure::cfg::cfg::CFG;
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::ir::*;

pub struct FieldElementComparisonWarning {
    file_id: FileID,
    file_location: FileLocation,
}

impl FieldElementComparisonWarning {
    pub fn produce_report(warning: FieldElementComparisonWarning) -> Report {
        let mut report = Report::warning(
            "comparisons with field elements greater than `p/2` may produce unexpected results".to_string(),

            ReportCode::FieldElementComparison,
        );
        report.add_primary(
            warning.file_location,
            warning.file_id,
            "field element comparison here".to_string(),
        );
        report.add_note(format!(
            "field elements `x` are always reduced modulo `p` and then normalized as `x > p/2? x - p: x` before they are compared"
        ));
        report
    }
}

/// Field element comparisons in Circom may produce surprising results since
/// elements are normalized to the the half-open interval `[-p/2, p/2)` before
/// they are compared. In particular, this means that
///
///   - `p/2 < 0`,
///   - `p/2 + 1 < p/2 - 1`, and
///   - `2 * x < x` for `p/4 < x < p/2`
///
/// are all true.
pub fn find_field_element_comparisons(cfg: &CFG) -> ReportCollection {
    let mut reports = ReportCollection::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            visit_statement(stmt, &mut reports);
        }
    }
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
        Return { .. } | Substitution { .. } | Declaration { .. } => (),
    }
}

fn visit_expression(expr: &Expression, reports: &mut ReportCollection) {
    use Expression::*;
    match expr {
        InfixOp { meta, infix_op, .. } if is_comparison_op(infix_op) => {
            reports.push(build_report(meta));
        },
        InfixOp { infix_op, rhe, lhe, .. } if is_boolean_infix_op(infix_op) => {
            visit_expression(lhe, reports);
            visit_expression(rhe, reports);
        }
        PrefixOp { prefix_op, rhe, ..} if is_boolean_prefix_op(prefix_op) => {
            visit_expression(rhe, reports);
        }
        _ => ()
    }
}

fn is_comparison_op(op: &ExpressionInfixOpcode) -> bool {
    use ExpressionInfixOpcode::*;
    matches!(op, LesserEq | GreaterEq | Lesser | Greater)
}

fn is_boolean_infix_op(op: &ExpressionInfixOpcode) -> bool {
    use ExpressionInfixOpcode::*;
    match op {
        BoolOr | BoolAnd => true,
        _ => false,
    }
}

fn is_boolean_prefix_op(op: &ExpressionPrefixOpcode) -> bool {
    use ExpressionPrefixOpcode::*;
    matches!(op, BoolNot)
}

fn build_report(meta: &Meta) -> Report {
    FieldElementComparisonWarning::produce_report(FieldElementComparisonWarning {
        file_id: meta.get_file_id(),
        file_location: meta.file_location(),
    })
}
