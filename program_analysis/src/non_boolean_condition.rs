#![deny(warnings)]
use log::debug;

use program_structure::cfg::Cfg;
use program_structure::report_code::ReportCode;
use program_structure::report::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::value_meta::ValueReduction;
use program_structure::ir::*;

pub struct NonBooleanConditionWarning {
    value: ValueReduction,
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl NonBooleanConditionWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            "Value used in boolean position may not be boolean.".to_string(),
            ReportCode::ConstantBranchCondition,
        );
        if let Some(file_id) = self.file_id {
            let msg = match self.value {
                ValueReduction::FieldElement(v) => format!(
                    "This value is a field element{}.",
                    if let Some(v) = v { format!(" equal to {v}") } else { "".to_string() }
                ),

                _ => "This value may or may not be a boolean".to_string(),
            };

            report.add_primary(self.file_location, file_id, msg);
        }
        report
    }
}

/// This analysis pass uses constant propagation to determine cases where
/// the expression in a condition may not be a Boolean.
pub fn find_non_boolean_conditional(cfg: &Cfg) -> ReportCollection {
    debug!("running non-boolean conditional analysis pass");
    let mut reports = ReportCollection::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            visit_statement(stmt, &mut reports);
        }
    }
    debug!("{} new reports generated", reports.len());
    reports
}

fn expect_boolean(e: &Expression, reports: &mut ReportCollection) {
    let value = e.meta().value_knowledge();
    if !matches!(value, ValueReduction::Boolean(_)) {
        reports.push(build_report(e.meta(), value.clone()));
    }
}

fn visit_statement(stmt: &Statement, reports: &mut ReportCollection) {
    use Statement::*;
    match stmt {
        IfThenElse { cond, .. } => {
            visit_expression(cond, reports);
            expect_boolean(cond, reports);
        }

        Declaration { dimensions, .. } => {
            for d in dimensions {
                visit_expression(d, reports);
            }
        }

        Return { value, .. } => visit_expression(value, reports),

        Substitution { rhe, .. } => visit_expression(rhe, reports),
        ConstraintEquality { lhe, rhe, .. } => {
            visit_expression(lhe, reports);
            visit_expression(rhe, reports);
        }
        LogCall { args, .. } => {
            for arg in args {
                if let LogArgument::Expr(e) = arg {
                    visit_expression(e, reports);
                }
            }
        }

        Assert { arg, .. } => visit_expression(arg, reports),
    }
}

fn visit_expression(e: &Expression, reports: &mut ReportCollection) {
    use Expression::*;
    match e {
        InfixOp { meta: _, lhe, infix_op, rhe } => {
            visit_expression(lhe, reports);
            visit_expression(rhe, reports);

            use ExpressionInfixOpcode::*;
            match infix_op {
                BoolOr | BoolAnd => {
                    expect_boolean(lhe, reports);
                    expect_boolean(rhe, reports);
                }
                _ => {}
            }
        }

        PrefixOp { meta: _, prefix_op, rhe } => {
            visit_expression(rhe, reports);
            if let ExpressionPrefixOpcode::BoolNot = prefix_op {
                expect_boolean(rhe, reports);
            }
        }

        SwitchOp { meta: _, cond, if_true, if_false } => {
            visit_expression(if_true, reports);
            visit_expression(if_false, reports);
            visit_expression(cond, reports);
            expect_boolean(cond, reports);
        }

        Call { args, .. } => {
            for a in args {
                visit_expression(a, reports);
            }
        }

        InlineArray { values, .. } => {
            for v in values {
                visit_expression(v, reports);
            }
        }

        Access { access, .. } => {
            for a in access {
                if let AccessType::ArrayAccess(e) = a {
                    visit_expression(e, reports);
                }
            }
        }

        Update { access, rhe, .. } => {
            for a in access {
                if let AccessType::ArrayAccess(e) = a {
                    visit_expression(e, reports);
                }
            }
            visit_expression(rhe, reports);
        }

        Phi { .. } => {}
        Variable { .. } => {}
        Number { .. } => {}
    }
}

fn build_report(meta: &Meta, value: ValueReduction) -> Report {
    NonBooleanConditionWarning {
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
    fn test_non_boolean_conditional() {
        let src = r#"
            function f(x) {
                var a = 1;
                var b = (2 * a * a + 1) << 2;
                var c = (3 * b / b - 2) >> 1;
                if (c >> 4 || x) {
                    a += x;
                    b += x * a;
                }
                return a + b;
            }
        "#;
        validate_reports(src, 2);

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
        let reports = find_non_boolean_conditional(&cfg);

        assert_eq!(reports.len(), expected_len);
    }
}
