use log::debug;

use program_structure::cfg::Cfg;
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::value_meta::ValueReduction;
use program_structure::ir::*;

pub struct ConstantBranchConditionWarning {
    value: bool,
    file_id: FileID,
    file_location: FileLocation,
}

impl ConstantBranchConditionWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            "Constant branching statement condition found.".to_string(),
            ReportCode::ConstantBranchCondition,
        );
        report.add_primary(
            self.file_location,
            self.file_id,
            format!("This condition is always {}.", self.value),
        );
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
    match stmt {
        IfThenElse { cond, .. } => {
            let value = cond.get_meta().get_value_knowledge().get_reduces_to();
            if let Some(Boolean { value }) = value {
                reports.push(build_report(cond.get_meta(), *value));
            }
        }
        _ => {}
    }
}

fn build_report(meta: &Meta, value: bool) -> Report {
    ConstantBranchConditionWarning {
        value,
        file_id: meta.get_file_id(),
        file_location: meta.file_location(),
    }
    .into_report()
}
