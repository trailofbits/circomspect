use std::collections::{HashMap, HashSet};

use log::debug;
use program_structure::cfg::Cfg;
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::intermediate_representation::variable_meta::VariableMeta;
use program_structure::report::{ReportCollection, Report};
use program_structure::ir::*;
use program_structure::report_code::ReportCode;

use crate::taint_analysis::{run_taint_analysis, TaintAnalysis};

const MIN_CONSTRAINT_COUNT: usize = 2;

#[derive(PartialEq, Eq, Hash)]
enum ConstraintLocation {
    Ordinary(FileLocation),
    Loop,
}

impl ConstraintLocation {
    fn file_location(&self) -> Option<FileLocation> {
        use ConstraintLocation::*;
        match self {
            Ordinary(file_location) => Some(file_location.clone()),
            Loop => None,
        }
    }
}

type ConstraintLocations = HashMap<VariableName, Vec<ConstraintLocation>>;

pub struct UnderConstrainedSignalWarning {
    name: VariableName,
    dimensions: Vec<Expression>,
    file_id: Option<FileID>,
    primary_location: FileLocation,
    secondary_location: Option<FileLocation>,
}

impl UnderConstrainedSignalWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            "Intermediate signals should typically occur in at least two separate constraints."
                .to_string(),
            ReportCode::UnderConstrainedSignal,
        );
        if let Some(file_id) = self.file_id {
            if self.dimensions.is_empty() {
                report.add_primary(
                    self.primary_location,
                    file_id,
                    format!("The intermediate signal `{}` is declared here.", self.name),
                );
                if let Some(secondary_location) = self.secondary_location {
                    report.add_secondary(
                        secondary_location,
                        file_id,
                        Some(format!(
                            "The intermediate signal `{}` is constrained here.",
                            self.name
                        )),
                    );
                }
            } else {
                report.add_primary(
                    self.primary_location,
                    file_id,
                    format!("The intermediate signal array `{}` is declared here.", self.name),
                );
                if let Some(secondary_location) = self.secondary_location {
                    report.add_secondary(
                        secondary_location,
                        file_id,
                        Some(format!(
                            "The intermediate signals in `{}` are constrained here.",
                            self.name
                        )),
                    );
                }
            }
        }
        report
    }
}

// Intermediate signals should occur in at least two separate constraints. One
// to define the value of the signal and one to constrain an input or output
// signal.
pub fn find_under_constrained_signals(cfg: &Cfg) -> ReportCollection {
    debug!("running under-constrained signals analysis pass");

    // Run taint analysis to be able to track data flow.
    let taint_analysis = run_taint_analysis(cfg);

    // Compute the set of intermediate signals.
    let mut constraint_locations = cfg
        .variables()
        .filter_map(|name| {
            if matches!(cfg.get_type(name), Some(VariableType::Signal(SignalType::Intermediate))) {
                Some((name.clone(), Vec::new()))
            } else {
                None
            }
        })
        .collect::<ConstraintLocations>();

    // Iterate through the CFG to identify intermediate signal constraints.
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            visit_statement(
                stmt,
                basic_block.in_loop(),
                &taint_analysis,
                &mut constraint_locations,
            );
        }
    }

    // Generate reports.
    let mut reports = ReportCollection::new();
    for (signal, locations) in constraint_locations {
        if locations.len() < MIN_CONSTRAINT_COUNT && !locations.contains(&ConstraintLocation::Loop)
        {
            let secondary_location =
                locations.first().and_then(|location| location.file_location());
            if let Some(declaration) = cfg.get_declaration(&signal) {
                reports.push(build_report(
                    &signal,
                    declaration.dimensions(),
                    declaration.file_id(),
                    declaration.file_location(),
                    secondary_location,
                ))
            }
        }
    }
    debug!("{} new reports generated", reports.len());
    reports
}

fn visit_statement(
    stmt: &Statement,
    in_loop: bool,
    taint_analysis: &TaintAnalysis,
    constraint_counts: &mut ConstraintLocations,
) {
    use AssignOp::*;
    use Statement::*;
    match stmt {
        // Update the constraint count for each intermediate signal. If the
        // statement occurs in a loop, we consider the minimum count to be
        // reached immediately.
        Substitution { meta, op: AssignConstraintSignal, .. } | ConstraintEquality { meta, .. } => {
            let sinks = stmt.variables_used().map(|var| var.name().clone()).collect::<HashSet<_>>();
            for (source, locations) in constraint_counts.iter_mut() {
                if taint_analysis.taints_any(source, &sinks) {
                    if in_loop {
                        locations.push(ConstraintLocation::Loop);
                    } else {
                        locations.push(ConstraintLocation::Ordinary(meta.file_location()))
                    }
                }
            }
        }
        _ => {}
    }
}

fn build_report(
    signal: &VariableName,
    dimensions: &[Expression],
    file_id: Option<FileID>,
    primary_location: FileLocation,
    secondary_location: Option<FileLocation>,
) -> Report {
    UnderConstrainedSignalWarning {
        name: signal.clone(),
        dimensions: dimensions.to_vec(),
        file_id,
        primary_location,
        secondary_location,
    }
    .into_report()
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::{cfg::IntoCfg, constants::Curve};

    use super::*;

    #[test]
    fn test_under_constrained_signals() {
        let src = r#"
            template Test(n) {
              signal input a;
              signal b;
              signal output c;

              c <== 2 * a;
            }
        "#;
        validate_reports(src, 1);

        let src = r#"
            template Test(n) {
              signal input a;
              signal b;
              signal output c;

              c <== a * b;
            }
        "#;
        validate_reports(src, 1);

        let src = r#"
            template Test(n) {
              signal input a;
              signal b;
              signal output c;

              b <== a * a;
              c <== a * b;
            }
        "#;
        validate_reports(src, 0);

        let src = r#"
            template Test(n) {
              signal input a[2];
              signal b;
              signal output c;

              var d = 2 * b;
              a[0] === d;
              a[1] === b + 1;
              c <== a[0] + a[1];
            }
        "#;
        validate_reports(src, 0);

        let src = r#"
            template Test(n) {
              signal input a[2];
              signal b[2];
              signal output c;

              for (var i = 0; i < 2; i++) {
                b[i] <== a[i];
              }
              c <== a[0] + a[1];
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
        let reports = find_under_constrained_signals(&cfg);
        assert_eq!(reports.len(), expected_len);
    }
}
