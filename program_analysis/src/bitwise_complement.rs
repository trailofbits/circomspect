use log::debug;

use program_structure::cfg::Cfg;
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::*;

pub struct BitwiseComplementWarning {
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl BitwiseComplementWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::info(
            "The bitwise complement is reduced modulo `p`, which means that `(~x)ᵢ != ~(xᵢ)` in general.".to_string(),
            ReportCode::FieldElementArithmetic,
        );
        if let Some(file_id) = self.file_id {
            report.add_primary(
                self.file_location,
                file_id,
                "256-bit complement taken here.".to_string(),
            );
        }
        report
    }
}

/// The output of `~x` is reduced modulo `p`, which means that individual bits
/// will typically not satisfy the expected relation `(~x)ᵢ != ~(xᵢ)`. This may
/// lead to unexpected results if the developer is not careful.
pub fn find_bitwise_complement(cfg: &Cfg) -> ReportCollection {
    debug!("running bitwise complement analysis pass");
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
    use ExpressionPrefixOpcode::*;
    match expr {
        PrefixOp { meta, prefix_op, .. } if matches!(prefix_op, Complement) => {
            reports.push(build_report(meta));
        }
        PrefixOp { rhe, .. } => {
            visit_expression(rhe, reports);
        }
        InfixOp { lhe, rhe, .. } => {
            visit_expression(lhe, reports);
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
            for access in access {
                if let AccessType::ArrayAccess(index) = access {
                    visit_expression(index, reports);
                }
            }
        }
        Update { access, rhe, .. } => {
            visit_expression(rhe, reports);
            for access in access {
                if let AccessType::ArrayAccess(index) = access {
                    visit_expression(index, reports);
                }
            }
        }
        Variable { .. } | Number(_, _) | Phi { .. } => (),
    }
}

fn build_report(meta: &Meta) -> Report {
    BitwiseComplementWarning { file_id: meta.file_id(), file_location: meta.file_location() }
        .into_report()
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::cfg::IntoCfg;

    use super::*;

    #[test]
    fn test_bitwise_complement() {
        let src = r#"
            function f() {
                return (1 > 2)? 3: ~4;
            }
        "#;
        validate_reports(src, 1);
    }

    fn validate_reports(src: &str, expected_len: usize) {
        // Build CFG.
        let mut reports = ReportCollection::new();
        let cfg =
            parse_definition(src).unwrap().into_cfg(&mut reports).unwrap().into_ssa().unwrap();
        assert!(reports.is_empty());

        // Generate report collection.
        let reports = find_bitwise_complement(&cfg);

        assert_eq!(reports.len(), expected_len);
    }
}
