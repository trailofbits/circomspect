use program_structure::cfg::Cfg;
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::*;

pub struct SignalAssignmentWarning {
    file_id: FileID,
    file_location: FileLocation,
}

impl SignalAssignmentWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            "using the signal assignment operator `<--` does not constrain the assigned signal"
                .to_string(),
            ReportCode::FieldElementComparison,
        );
        report.add_primary(
            self.file_location,
            self.file_id,
            "did you mean to use the constraint assignment operator `<==`?".to_string(),
        );
        report
    }
}

/// The signal assignment operator `y <-- x` does not constrain the signal `y`.
/// If the developer meant to use the constraint assignment operator `<==` this
/// could lead to unexpected results.
pub fn find_signal_assignments(cfg: &Cfg) -> ReportCollection {
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
        Substitution { meta, op, .. } if is_assign_signal_op(op) => {
            reports.push(build_report(meta));
        }
        _ => {}
    }
}

fn is_assign_signal_op(op: &AssignOp) -> bool {
    matches!(op, AssignOp::AssignSignal)
}

fn build_report(meta: &Meta) -> Report {
    SignalAssignmentWarning {
        file_id: meta.get_file_id(),
        file_location: meta.file_location(),
    }
    .into_report()
}
