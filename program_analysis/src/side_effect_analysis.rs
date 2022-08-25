use log::debug;
use std::collections::HashSet;

use program_structure::cfg::Cfg;
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::variable_meta::VariableUse;
use program_structure::ir::{SignalType, Statement, VariableName, VariableType};

use crate::taint_analysis::run_taint_analysis;

pub struct UnusedVariableWarning {
    name: String,
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl UnusedVariableWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            format!(
                "The variable `{}` is assigned a value, but this value is never read.",
                self.name
            ),
            ReportCode::UnusedVariableValue,
        );
        if let Some(file_id) = self.file_id {
            report.add_primary(
                self.file_location,
                file_id,
                "The value assigned here is never read.".to_string(),
            );
        }
        report
    }
}

pub struct UnusedParameterWarning {
    function_name: String,
    variable_name: String,
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl UnusedParameterWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            format!("The parameter `{}` is never read.", self.variable_name),
            ReportCode::UnusedParameterValue,
        );
        if let Some(file_id) = self.file_id {
            report.add_primary(
                self.file_location,
                file_id,
                format!(
                    "The value of `{}` is never used in `{}`.",
                    self.variable_name, self.function_name
                ),
            );
        }
        report
    }
}

pub struct NoSideEffectsWarning {
    name: String,
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl NoSideEffectsWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            format!(
                "The value assigned to `{}` is not used in either witness or constraint generation.",
                self.name
            ),
            ReportCode::NoSideEffectFromAssignment,
        );
        if let Some(file_id) = self.file_id {
            report.add_primary(
                self.file_location,
                file_id,
                format!("The variable `{}` could be removed.", self.name),
            );
        }
        report
    }
}
/// Local variables and intermediate signals that do not flow into either
///
///   1. an output signal,
///   2. a constraint,
///   3. a return value, or
///   4. a control-flow condition
///
/// are side-effect free and do not affect either witness or constraint
/// generation.
pub fn run_side_effect_analysis(cfg: &Cfg) -> ReportCollection {
    debug!("running side-effect analysis pass");

    // Run taint analysis to be able to track data flow.
    let taint_analysis = run_taint_analysis(cfg);

    // Initialize sinks with all output signals.
    use SignalType::Output;
    use VariableType::Signal;
    let mut sinks: HashSet<VariableName> = HashSet::from_iter(cfg
        .declarations()
        .iter()
        .filter_map(|(name, declaration)|
            if matches!(declaration.variable_type(), Signal { signal_type, .. } if *signal_type == Output) {
                Some(name.clone())
            } else {
                None
            }
        )
    );
    // Update sinks with all variables occurring in constraints or as return values.
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            use Statement::*;
            match stmt {
                // TODO: Restrict to constraints which affect input or output
                // signals, either directly or indirectly. Also, consider adding
                // `Assert`.
                ConstraintEquality { meta, .. } | IfThenElse { meta, .. } | Return { meta, .. } => {
                    sinks.extend(
                        meta.variable_knowledge()
                            .variables_read()
                            .map(|var| var.name().clone()),
                    );
                }
                _ => {}
            }
        }
    }

    let mut reports = ReportCollection::new();
    for source in taint_analysis.definitions() {
        // If the source is also a sink we break early.
        if sinks.contains(source.name()) {
            continue;
        } else if taint_analysis.single_step_taint(source.name()).is_empty() {
            // If the variable doesn't flow to anything at all, it is unused.
            if cfg.parameters().contains(source.name()) {
                reports.push(build_unused_param(cfg.name(), source))
            } else {
                reports.push(build_unused_variable(source));
            }
        } else if !taint_analysis.taints_any(source.name(), &sinks) {
            // If a variable doesn't flow to any of the defined sinks, it is side-effect free.
            reports.push(build_no_side_effect(source));
        }
    }
    reports
}

fn build_unused_variable(definition: &VariableUse) -> Report {
    UnusedVariableWarning {
        name: definition.name().to_string(),
        file_id: definition.meta().file_id(),
        file_location: definition.meta().file_location(),
    }
    .into_report()
}

fn build_unused_param(function_name: &str, definition: &VariableUse) -> Report {
    UnusedParameterWarning {
        function_name: function_name.to_string(),
        variable_name: definition.name().to_string(),
        file_id: definition.meta().file_id(),
        file_location: definition.meta().file_location(),
    }
    .into_report()
}

fn build_no_side_effect(definition: &VariableUse) -> Report {
    NoSideEffectsWarning {
        name: definition.name().to_string(),
        file_id: definition.meta().file_id(),
        file_location: definition.meta().file_location(),
    }
    .into_report()
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::cfg::IntoCfg;

    use super::*;

    #[test]
    fn test_side_effect_analysis() {
        let src = r#"
            template T(n) {
              signal input in;
              signal output out[n];

              var lin = 0;
              var lout = 0;  // The value assigned here is side-effect free.

              var e = 1;  // The value assigned here is side-effect free.
              for (var k = 0; k < n; k++) {
                out[k] <-- (in >> k) & 1;
                out[k] * (out[k] - 1) === 0;

                lout += out[k] * e;  // The value assigned here is side-effect free.
                e = e + e;  // The value assigned here is side-effect free.
              }

              lin === nout;  // Should use `lout`, but uses `nout` by mistake.
            }
        "#;
        validate_reports(src, 3);
    }

    fn validate_reports(src: &str, expected_len: usize) {
        // Build CFG.
        let mut reports = ReportCollection::new();
        let cfg = parse_definition(src)
            .unwrap()
            .into_cfg(&mut reports)
            .unwrap()
            .into_ssa()
            .unwrap();
        assert!(reports.is_empty());

        // Generate report collection.
        let reports = run_side_effect_analysis(&cfg);
        for report in &reports {
            println!("{:?}", report.get_message());
        }
        assert_eq!(reports.len(), expected_len);
    }
}
