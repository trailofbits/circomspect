use log::{debug, trace};
use program_structure::ir::AccessType;
use std::collections::HashSet;

use program_structure::cfg::Cfg;
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::ir::variable_meta::VariableMeta;
use program_structure::ir::*;

pub struct SignalAssignmentWarning {
    signal: VariableName,
    access: Vec<AccessType>,
    assignment_meta: Meta,
    constraint_metas: Vec<Meta>,
}

impl SignalAssignmentWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            "Using the signal assignment operator `<--` does not constrain the assigned signal."
                .to_string(),
            ReportCode::FieldElementComparison,
        );
        // Add signal assignment warning.
        if let Some(file_id) = self.assignment_meta.file_id {
            report.add_primary(
                self.assignment_meta.location,
                file_id,
                format!(
                    "The assigned signal `{}{}` is not constrained here.",
                    self.signal,
                    access_to_string(&self.access)
                ),
            );
        }
        // Add any constraints as secondary labels.
        for meta in self.constraint_metas {
            if let Some(file_id) = meta.file_id {
                report.add_secondary(
                    meta.location,
                    file_id,
                    Some(format!(
                        "The signal `{}{}` is constrained here.",
                        self.signal,
                        access_to_string(&self.access),
                    )),
                );
            }
        }
        // If no constraints are identified, suggest using `<==` instead.
        if report.get_secondary().is_empty() {
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
    pub access: Vec<AccessType>,
}

impl Assignment {
    fn new(meta: &Meta, signal: &VariableName, access: &[AccessType]) -> Assignment {
        Assignment { meta: meta.clone(), signal: signal.clone(), access: access.to_owned() }
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
        Constraint { meta: meta.clone(), lhe: lhe.clone(), rhe: rhe.clone() }
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
    fn add_assignment(&mut self, var: &VariableName, access: &[AccessType], meta: &Meta) {
        trace!("adding signal assignment for `{var}` access");
        self.assignments.insert(Assignment::new(meta, var, access));
    }

    /// Add a constraint `lhe === rhe`.
    fn add_constraint(&mut self, lhe: &Expression, rhe: &Expression, meta: &Meta) {
        trace!("adding constraint `{lhe} === {rhe}`");
        self.constraints.insert(Constraint::new(meta, lhe, rhe));
    }

    /// Get all assignments.
    fn get_assignments(&self) -> &AssignmentSet {
        &self.assignments
    }

    /// Get the set of constraints that contain the given variable.
    fn get_constraints(&self, signal: &VariableName, access: &Vec<AccessType>) -> Vec<&Constraint> {
        self.constraints
            .iter()
            .filter(|constraint| {
                let lhe = constraint.lhe.signals_read().iter();
                let rhe = constraint.rhe.signals_read().iter();
                lhe.chain(rhe)
                    .any(|signal_use| signal_use.name() == signal && signal_use.access() == access)
            })
            .collect()
    }

    /// Returns the corresponding `Meta` of a constraint containing the given
    /// signal, or `None` if no such constraint exists.
    fn get_constraint_metas(&self, signal: &VariableName, access: &Vec<AccessType>) -> Vec<Meta> {
        self.get_constraints(signal, access)
            .iter()
            .map(|constraint| constraint.meta.clone())
            .collect()
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
        let constraint_meta =
            signal_data.get_constraint_metas(&assignment.signal, &assignment.access);
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
    use Expression::*;
    use Statement::*;
    match stmt {
        Substitution { meta, var, op, rhe: Update { access, rhe, .. } } => {
            match op {
                AssignOp::AssignSignal => {
                    signal_data.add_assignment(var, access, meta);
                }
                // A signal cannot occur as the LHS of both a signal assignment
                // and a signal constraint assignment. However, we still need to
                // record the constraint added for each constraint assignment
                // found.
                AssignOp::AssignConstraintSignal => {
                    let lhe = Expression::Variable { meta: meta.clone(), name: var.clone() };
                    signal_data.add_constraint(&lhe, rhe, meta)
                }
                AssignOp::AssignLocalOrComponent => {}
            }
        }
        Substitution { meta, var, op, rhe } => {
            match op {
                AssignOp::AssignSignal => {
                    signal_data.add_assignment(var, &Vec::new(), meta);
                }
                // A signal cannot occur as the LHS of both a signal assignment
                // and a signal constraint assignment. However, we still need to
                // record the constraint added for each constraint assignment
                // found.
                AssignOp::AssignConstraintSignal => {
                    let lhe = Expression::Variable { meta: meta.clone(), name: var.clone() };
                    signal_data.add_constraint(&lhe, rhe, meta)
                }
                AssignOp::AssignLocalOrComponent => {}
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
    access: &[AccessType],
    assignment_meta: &Meta,
    constraint_metas: &[Meta],
) -> Report {
    SignalAssignmentWarning {
        signal: signal.clone(),
        access: access.to_owned(),
        assignment_meta: assignment_meta.clone(),
        constraint_metas: constraint_metas.to_owned(),
    }
    .into_report()
}

#[must_use]
fn access_to_string(access: &[AccessType]) -> String {
    access.iter().map(|access| access.to_string()).collect::<Vec<String>>().join("")
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::cfg::IntoCfg;

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
        let mut reports = ReportCollection::new();
        let cfg =
            parse_definition(src).unwrap().into_cfg(&mut reports).unwrap().into_ssa().unwrap();
        assert!(reports.is_empty());

        // Generate report collection.
        let reports = find_signal_assignments(&cfg);

        assert_eq!(reports.len(), expected_len);
    }
}
