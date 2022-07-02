use log::debug;
use std::collections::HashSet;

use program_structure::cfg::Cfg;
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::ir::variable_meta::VariableMeta;
use program_structure::ir::*;

pub struct SignalAssignmentWarning {
    signal: VariableName,
    assignment_meta: Meta,
    constraint_meta: Option<Meta>,
}

impl SignalAssignmentWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            "Using the signal assignment operator `<--` does not constrain the assigned signal."
                .to_string(),
            ReportCode::FieldElementComparison,
        );
        if let Some(file_id) = self.assignment_meta.file_id {
            report.add_primary(
                self.assignment_meta.location,
                file_id,
                format!(
                    "The assigned signal `{}` is not constrained here.",
                    self.signal
                ),
            );
        }
        if let Some(Meta {
            file_id: Some(file_id),
            location,
            ..
        }) = self.constraint_meta
        {
            report.add_secondary(
                location,
                file_id,
                Some(format!("The signal `{}` is constrained here.", self.signal)),
            );
        } else {
            report.add_note(
                "Consider using the constraint assignment operator `<==` instead.".to_string(),
            );
        }
        report
    }
}

/// This structure tracks signal assignments and constraints in a single
/// template.
#[derive(Clone, Default)]
struct ConstraintInfo {
    assignments: HashSet<(VariableName, Vec<Access>, Meta)>,
    constraints: HashSet<(Expression, Expression, Meta)>,
}

impl ConstraintInfo {
    /// Create a new `ConstraintInfo` instance.
    fn new() -> ConstraintInfo {
        ConstraintInfo::default()
    }

    /// Add an assignment `signal <-- expr`.
    fn add_assignment(&mut self, var: &VariableName, access: &Vec<Access>, meta: &Meta) {
        self.assignments
            .insert((var.clone(), access.clone(), meta.clone()));
    }

    /// Add a constraint `expr === expr`.
    fn add_constraint(&mut self, lhe: &Expression, rhe: &Expression, meta: &Meta) {
        self.constraints
            .insert((lhe.clone(), rhe.clone(), meta.clone()));
    }

    /// Get all assignments.
    fn get_assignments(&self) -> &HashSet<(VariableName, Vec<Access>, Meta)> {
        &self.assignments
    }

    /// Get the set of constraints that contain the given variable.
    fn get_constraints(&self, signal: &VariableName) -> Vec<(&Expression, &Expression, &Meta)> {
        let mut constraints = Vec::new();
        for (lhe, rhe, meta) in &self.constraints {
            if lhe.get_signals_read().contains(signal) || rhe.get_signals_read().contains(signal) {
                constraints.push((lhe, rhe, meta));
            }
        }
        constraints
    }

    /// Returns the corresponding `Meta` of a constraint containing the given
    /// signal, or `None` if no such constraint exists.
    fn has_constraint(&self, signal: &VariableName) -> Option<Meta> {
        for (lhe, rhe, meta) in self.get_constraints(signal) {
            if lhe.get_signals_read().contains(signal) || rhe.get_signals_read().contains(signal) {
                return Some(meta.clone());
            }
        }
        None
    }
}

/// The signal assignment operator `y <-- x` does not constrain the signal `y`.
/// If the developer meant to use the constraint assignment operator `<==` this
/// could lead to unexpected results.
pub fn find_signal_assignments(cfg: &Cfg) -> ReportCollection {
    debug!("running signal assignment analysis pass");

    let mut constraints = ConstraintInfo::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            visit_statement(stmt, &mut constraints);
        }
    }
    let mut reports = ReportCollection::new();
    for (signal, assignment_access, assignment_meta) in constraints.get_assignments() {
        let constraint_meta = constraints.has_constraint(signal);
        reports.push(build_report(signal, assignment_access, assignment_meta, &constraint_meta));
    }

    debug!("{} new reports generated", reports.len());
    reports
}

fn visit_statement(stmt: &Statement, constraints: &mut ConstraintInfo) {
    use Statement::*;
    match stmt {
        Substitution {
            meta,
            var,
            access,
            op,
            ..
        } => {
            match op {
                AssignOp::AssignSignal => {
                    constraints.add_assignment(var, access, meta);
                }
                // A signal cannot occur as the LHS of both a `<--` and a
                // `<==` statement, so we ignore constraint assignments.
                AssignOp::AssignVar | AssignOp::AssignConstraintSignal => {}
            }
        }
        ConstraintEquality { meta, lhe, rhe } => {
            constraints.add_constraint(lhe, rhe, meta);
        }
        _ => {}
    }
}

fn build_report(
    signal: &VariableName,
    assignment_access: &Vec<Access>,
    assignment_meta: &Meta,
    constraint_meta: &Option<Meta>,
) -> Report {
    // TODO: determine matching constraints for array accesses.
    if assignment_access.is_empty() {
        SignalAssignmentWarning {
            signal: signal.clone(),
            assignment_meta: assignment_meta.clone(),
            constraint_meta: constraint_meta.clone(),
        }
        .into_report()
    } else {
        SignalAssignmentWarning {
            signal: signal.clone(),
            assignment_meta: assignment_meta.clone(),
            constraint_meta: None,
        }
        .into_report()
    }
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;

    use super::*;

    #[test]
    fn test_field_comparisons() {
        let src = r#"
            template t(a) {
                signal input in;
                signal output out;

                out <-- in + a;
            }
        "#;
        validate_reports(src, 1);

        let src = r#"
            template t(a) {
                signal input in;
                signal output out;

                in + a === out;
                out <-- in + a;
            }
        "#;
        validate_reports(src, 1);

        let src = r#"
            template t(n) {
                signal input in;
                signal output out[n];

                in + 1 === out[0];
                out[0] <-- in + 1;
            }
        "#;
        validate_reports(src, 1);
    }

    fn validate_reports(src: &str, expected_len: usize) {
        // Build CFG.
        let (cfg, _) = parse_definition(src).unwrap().try_into().unwrap();
        let cfg = cfg.into_ssa().unwrap();

        // Generate report collection.
        let reports = find_signal_assignments(&cfg);

        assert_eq!(reports.len(), expected_len);
    }
}
