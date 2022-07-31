use log::debug;
use program_structure::ir::Access;
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

type AssignmentSet = HashSet<Assignment>;
/// A signal assignment (implemented using either `<--` or `<==`).
#[derive(Clone, Hash, PartialEq, Eq)]
struct Assignment {
    pub meta: Meta,
    pub signal: VariableName,
    pub access: Vec<Access>,
}

impl Assignment {
    fn new(meta: &Meta, signal: &VariableName, access: &Vec<Access>) -> Assignment {
        Assignment {
            meta: meta.clone(),
            signal: signal.clone(),
            access: access.clone(),
        }
    }
}

type ConstraintSet = HashSet<Constraint>;

#[derive(Clone, Hash, PartialEq, Eq)]
struct Constraint {
    pub meta: Meta,
    pub lhe: Expression,
    pub rhe: Expression,
}

impl Constraint {
    fn new(meta: &Meta, lhe: &Expression, rhe: &Expression) -> Constraint {
        Constraint {
            meta: meta.clone(),
            lhe: lhe.clone(),
            rhe: rhe.clone(),
        }
    }
}

/// This structure tracks signal assignments and constraints in a single
/// template.
#[derive(Clone, Default)]
struct SignalData {
    assignments: AssignmentSet,
    constraints: ConstraintSet,
}

impl SignalData {
    /// Create a new `ConstraintInfo` instance.
    fn new() -> SignalData {
        SignalData::default()
    }

    /// Add an assignment `var[access] <-- expr`.
    fn add_assignment(&mut self, var: &VariableName, access: &Vec<Access>, meta: &Meta) {
        self.assignments.insert(Assignment::new(meta, var, access));
    }

    /// Add a constraint `lhe === rhe`.
    fn add_constraint(&mut self, lhe: &Expression, rhe: &Expression, meta: &Meta) {
        self.constraints.insert(Constraint::new(meta, lhe, rhe));
    }

    /// Get all assignments.
    fn get_assignments(&self) -> &AssignmentSet {
        &self.assignments
    }

    /// Get the set of constraints that contain the given variable.
    fn get_constraints(&self, signal: &VariableName) -> Vec<&Constraint> {
        self.constraints
            .iter()
            .filter(|constraint| {
                let lhe = constraint.lhe.get_signals_read().iter();
                let rhe = constraint.rhe.get_signals_read().iter();
                lhe.chain(rhe)
                    .any(|signal_use| signal_use.get_name() == &signal.clone())
            })
            .collect()
    }

    /// Returns the corresponding `Meta` of a constraint containing the given
    /// signal, or `None` if no such constraint exists.
    fn has_constraint(&self, signal: &VariableName) -> Option<Meta> {
        self.get_constraints(signal)
            .iter()
            .next()
            .map(|constraint| constraint.meta.clone())
    }
}

/// The signal assignment operator `y <-- x` does not constrain the signal `y`.
/// If the developer meant to use the constraint assignment operator `<==` this
/// could lead to unexpected results.
pub fn find_signal_assignments(cfg: &Cfg) -> ReportCollection {
    debug!("running signal assignment analysis pass");

    let mut signal_data = SignalData::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            visit_statement(stmt, &mut signal_data);
        }
    }
    let mut reports = ReportCollection::new();
    for assignment in signal_data.get_assignments() {
        let constraint_meta = signal_data.has_constraint(&assignment.signal);
        reports.push(build_report(
            &assignment.signal,
            &assignment.access,
            &assignment.meta,
            &constraint_meta,
        ));
    }

    debug!("{} new reports generated", reports.len());
    reports
}

fn visit_statement(stmt: &Statement, signal_data: &mut SignalData) {
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
                    signal_data.add_assignment(var, access, meta);
                }
                // A signal cannot occur as the LHS of both a `<--` and a
                // `<==` statement, so we ignore constraint assignments.
                AssignOp::AssignVar
                | AssignOp::AssignComponent
                | AssignOp::AssignConstraintSignal => {}
            }
        }
        ConstraintEquality { meta, lhe, rhe } => {
            signal_data.add_constraint(lhe, rhe, meta);
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
