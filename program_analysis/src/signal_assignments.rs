use log::{debug, trace};
use program_structure::intermediate_representation::degree_meta::{DegreeRange, DegreeMeta};
use std::collections::HashSet;

use program_structure::cfg::{Cfg, DefinitionType};
use program_structure::report_code::ReportCode;
use program_structure::report::{Report, ReportCollection};
use program_structure::ir::*;
use program_structure::ir::AccessType;
use program_structure::ir::degree_meta::Degree;
use program_structure::ir::variable_meta::VariableMeta;

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
            ReportCode::SignalAssignmentStatement,
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
        if report.secondary().is_empty() {
            report.add_note(
                "Consider if it is possible to rewrite the statement using `<==` instead."
                    .to_string(),
            );
        }
        report
    }
}

pub struct UnecessarySignalAssignmentWarning {
    signal: VariableName,
    access: Vec<AccessType>,
    assignment_meta: Meta,
}

impl UnecessarySignalAssignmentWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            "Using the signal assignment operator `<--` is not necessary here.".to_string(),
            ReportCode::UnecessarySignalAssignment,
        );
        // Add signal assignment warning.
        if let Some(file_id) = self.assignment_meta.file_id {
            report.add_primary(
                self.assignment_meta.location,
                file_id,
                format!(
                    "The expression assigned to `{}{}` is quadratic.",
                    self.signal,
                    access_to_string(&self.access)
                ),
            );
        }
        // We always suggest using `<==` instead.
        report.add_note(
            "Consider rewriting the statement using the constraint assignment operator `<==`."
                .to_string(),
        );
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
    pub degree: Option<DegreeRange>,
}

impl Assignment {
    fn new(
        meta: &Meta,
        signal: &VariableName,
        access: &[AccessType],
        degree: Option<&DegreeRange>,
    ) -> Assignment {
        Assignment {
            meta: meta.clone(),
            signal: signal.clone(),
            access: access.to_owned(),
            degree: degree.cloned(),
        }
    }

    fn is_quadratic(&self) -> bool {
        if let Some(range) = &self.degree {
            range.end() <= Degree::Quadratic
        } else {
            false
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
        Constraint { meta: meta.clone(), lhe: lhe.clone(), rhe: rhe.clone() }
    }
}

/// This structure tracks signal assignments and constraints in a single
/// template.
#[derive(Clone, Default)]
struct SignalUse {
    assignments: AssignmentSet,
    constraints: ConstraintSet,
}

impl SignalUse {
    /// Create a new `ConstraintInfo` instance.
    fn new() -> SignalUse {
        SignalUse::default()
    }

    /// Add a signal assignment `var[access] <-- expr`.
    fn add_assignment(
        &mut self,
        var: &VariableName,
        access: &[AccessType],
        meta: &Meta,
        degree: Option<&DegreeRange>,
    ) {
        trace!("adding signal assignment for `{var:?}` access");
        self.assignments.insert(Assignment::new(meta, var, access, degree));
    }

    /// Add a constraint `lhe === rhe`.
    fn add_constraint(&mut self, lhe: &Expression, rhe: &Expression, meta: &Meta) {
        trace!("adding constraint `{lhe:?} === {rhe:?}`");
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
    use DefinitionType::*;
    if matches!(cfg.definition_type(), Function | CustomTemplate) {
        // Exit early if this is a function or custom template.
        return ReportCollection::new();
    }
    debug!("running signal assignment analysis pass");
    let mut signal_use = SignalUse::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            visit_statement(stmt, &mut signal_use);
        }
    }
    let mut reports = ReportCollection::new();
    for assignment in signal_use.get_assignments() {
        if assignment.is_quadratic() {
            reports.push(build_unecessary_assignment_report(
                &assignment.signal,
                &assignment.access,
                &assignment.meta,
            ))
        } else {
            let constraint_metas =
                signal_use.get_constraint_metas(&assignment.signal, &assignment.access);
            reports.push(build_assignment_report(
                &assignment.signal,
                &assignment.access,
                &assignment.meta,
                &constraint_metas,
            ));
        }
    }

    debug!("{} new reports generated", reports.len());
    reports
}

fn visit_statement(stmt: &Statement, signal_use: &mut SignalUse) {
    use Expression::*;
    use Statement::*;
    match stmt {
        Substitution { meta, var, op, rhe } => {
            let access = if let Update { access, .. } = rhe { access.clone() } else { Vec::new() };
            match op {
                AssignOp::AssignSignal => {
                    signal_use.add_assignment(var, &access, meta, rhe.degree());
                }
                // A signal cannot occur as the LHS of both a signal assignment
                // and a signal constraint assignment. However, we still need to
                // record the constraint added for each constraint assignment
                // found.
                AssignOp::AssignConstraintSignal => {
                    let lhe = Expression::Variable { meta: meta.clone(), name: var.clone() };
                    signal_use.add_constraint(&lhe, rhe, meta)
                }
                AssignOp::AssignLocalOrComponent => {}
            }
        }
        ConstraintEquality { meta, lhe, rhe } => {
            signal_use.add_constraint(lhe, rhe, meta);
        }
        _ => {}
    }
}

fn build_unecessary_assignment_report(
    signal: &VariableName,
    access: &[AccessType],
    assignment_meta: &Meta,
) -> Report {
    UnecessarySignalAssignmentWarning {
        signal: signal.clone(),
        access: access.to_owned(),
        assignment_meta: assignment_meta.clone(),
    }
    .into_report()
}

fn build_assignment_report(
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
    use program_structure::{cfg::IntoCfg, constants::Curve};

    use super::*;

    #[test]
    fn test_signal_assignments() {
        let src = r#"
            template T(a) {
                signal input in;
                signal output out;

                out <-- in + a;
            }
        "#;
        validate_reports(src, 1);

        let src = r#"
            template T(a) {
                signal input in;
                signal output out;

                in + a === out;
                out <-- in + a;
            }
        "#;
        validate_reports(src, 1);

        let src = r#"
            template T(n) {
                signal input in;
                signal output out[n];

                in + 1 === out[0];
                out[0] <-- in + 1;
            }
        "#;
        validate_reports(src, 1);

        let src = r#"
            template T(n) {
                signal output out[n];

                in + 1 === out[0];
                out[0] <-- in * in;
            }
        "#;
        validate_reports(src, 1);
    }

    fn validate_reports(src: &str, expected_len: usize) {
        // Build CFG.
        println!("{}", src);
        let mut reports = ReportCollection::new();
        let cfg = parse_definition(src)
            .unwrap()
            .into_cfg(&Curve::default(), &mut reports)
            .unwrap()
            .into_ssa()
            .unwrap();
        assert!(reports.is_empty());

        // Generate report collection.
        let reports = find_signal_assignments(&cfg);
        for report in &reports {
            println!("{}", report.message())
        }

        assert_eq!(reports.len(), expected_len);
    }
}
