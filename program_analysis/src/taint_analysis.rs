use log::{debug, trace};
use program_structure::cfg::parameters::Parameters;
use program_structure::intermediate_representation::value_meta::ValueMeta;
use program_structure::intermediate_representation::Meta;
use std::collections::{HashMap, HashSet};

use program_structure::cfg::Cfg;
use program_structure::ir::variable_meta::{VariableMeta, VariableUse};
use program_structure::ir::{Expression, Statement, VariableName};

#[derive(Clone, Default)]
pub struct TaintAnalysis {
    taint_map: HashMap<VariableName, HashSet<VariableName>>,
    declarations: HashMap<VariableName, VariableUse>,
    definitions: HashMap<VariableName, VariableUse>,
}

impl TaintAnalysis {
    fn new(parameters: &Parameters) -> TaintAnalysis {
        // Add parameter definitions to taint analysis.
        let mut result = TaintAnalysis::default();
        let meta = Meta::new(parameters.file_location(), parameters.file_id());
        for name in parameters.iter() {
            trace!("adding parameter declaration for `{name:?}`");
            let definition = VariableUse::new(&meta, name, &Vec::new());
            result.add_definition(&definition);
        }
        result
    }

    /// Add the variable use corresponding to the definition of the variable.
    fn add_definition(&mut self, var: &VariableUse) {
        // TODO: Since we don't version components and signals, we may end up
        // overwriting component initializations here. For example, in the
        // following case the component initialization will be clobbered.
        //
        //   component c[2];
        //   ...
        //   c[0].in[0] <== 0;
        //   c[1].in[1] <== 1;
        //
        // As long as the initialized component flows to a constraint it will
        // not be flagged during side-effect analysis.
        self.definitions.insert(var.name().clone(), var.clone());
    }

    /// Get the variable use corresponding to the definition of the variable.
    pub fn get_definition(&self, var: &VariableName) -> Option<VariableUse> {
        self.definitions.get(var).cloned()
    }

    pub fn definitions(&self) -> impl Iterator<Item = &VariableUse> {
        self.definitions.values()
    }

    /// Add the variable use corresponding to the declaration of the variable.
    fn add_declaration(&mut self, var: &VariableUse) {
        self.declarations.insert(var.name().clone(), var.clone());
    }

    /// Get the variable use corresponding to the declaration of the variable.
    pub fn get_declaration(&self, var: &VariableName) -> Option<VariableUse> {
        self.declarations.get(var).cloned()
    }

    pub fn declarations(&self) -> impl Iterator<Item = &VariableUse> {
        self.declarations.values()
    }

    /// Add a single step taint from source to sink.
    fn add_taint_step(&mut self, source: &VariableName, sink: &VariableName) {
        let sinks = self.taint_map.entry(source.clone()).or_default();
        sinks.insert(sink.clone());
    }

    /// Returns variables tainted in a single step by `source`.
    pub fn single_step_taint(&self, source: &VariableName) -> HashSet<VariableName> {
        self.taint_map.get(source).cloned().unwrap_or_default()
    }

    /// Returns variables tainted in zero or more steps by `source`.
    pub fn multi_step_taint(&self, source: &VariableName) -> HashSet<VariableName> {
        let mut result = HashSet::new();
        let mut update = HashSet::from([source.clone()]);
        while !update.is_subset(&result) {
            result.extend(update.iter().cloned());
            update = update.iter().flat_map(|source| self.single_step_taint(source)).collect();
        }
        result
    }

    /// Returns true if the source taints any of the sinks.
    pub fn taints_any(&self, source: &VariableName, sinks: &HashSet<VariableName>) -> bool {
        self.multi_step_taint(source).iter().any(|sink| sinks.contains(sink))
    }
}

pub fn run_taint_analysis(cfg: &Cfg) -> TaintAnalysis {
    debug!("running taint analysis pass");
    let mut result = TaintAnalysis::new(cfg.parameters());

    use Expression::*;
    use Statement::*;
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            trace!("visiting statement `{stmt:?}`");
            match stmt {
                Substitution { .. } => {
                    // Variables read taint variables written by the statement.
                    for sink in stmt.variables_written() {
                        if !matches!(stmt, Substitution { rhe: Phi { .. }, .. }) {
                            // Add the definition to the result.
                            trace!("adding variable assignment for `{:?}`", sink.name());
                            result.add_definition(sink);
                        }
                        for source in stmt.variables_read() {
                            // Add each taint step to the result.
                            trace!(
                                "adding taint step with source `{:?}` and sink `{:?}`",
                                source.name(),
                                sink.name()
                            );
                            result.add_taint_step(source.name(), sink.name());
                        }
                    }
                }
                Declaration { meta, names, dimensions, .. } => {
                    // Variables occurring in declarations taint the declared variable.
                    for sink in names {
                        result.add_declaration(&VariableUse::new(meta, sink, &Vec::new()));
                        for size in dimensions {
                            for source in size.variables_read() {
                                result.add_taint_step(source.name(), sink)
                            }
                        }
                    }
                }
                IfThenElse { cond, .. } => {
                    // A variable which occurs in a non-constant condition taints all
                    // variables assigned in the if-statement body.
                    if cond.value().is_some() {
                        continue;
                    }
                    let true_branch = cfg.get_true_branch(basic_block);
                    let false_branch = cfg.get_false_branch(basic_block);
                    for body in true_branch.iter().chain(false_branch.iter()) {
                        // Add taint for assigned variables.
                        for sink in body.variables_written() {
                            for source in cond.variables_read() {
                                // Add each taint step to the result.
                                trace!(
                                    "adding taint step with source `{:?}` and sink `{:?}`",
                                    source.name(),
                                    sink.name()
                                );
                                result.add_taint_step(source.name(), sink.name());
                            }
                        }
                    }
                }
                // The following statement types do not propagate taint.
                Assert { .. } | LogCall { .. } | Return { .. } | ConstraintEquality { .. } => {}
            }
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use parser::parse_definition;
    use program_structure::cfg::IntoCfg;
    use program_structure::constants::Curve;
    use program_structure::report::ReportCollection;

    use super::*;

    #[test]
    fn test_taint_analysis() {
        let src = r#"
            template PointOnLine(k, m, n) {
                signal input in[2];

                var LOGK = log2(k);
                var LOGK2 = log2(3 * k * k);
                assert(3 * n + LOGK2 < 251);

                component left = BigTemplate(n, k, 2 * n + LOGK + 1);
                left.a <== in[0];
                left.b <== in[1];

                component right[m];
                for (var i = 0; i < n; i++) {
                    right[0] = SmallTemplate(k);
                }
            }
        "#;

        let mut taint_map = HashMap::new();
        taint_map.insert(
            "k",
            HashSet::from([
                "k".to_string(),
                "LOGK".to_string(),
                "LOGK2".to_string(),
                "left".to_string(),
                "right".to_string(),
            ]),
        );
        taint_map.insert(
            "m",
            HashSet::from([
                "m".to_string(),
                "right".to_string(), // Since `right` is declared as an `m` dimensional array.
            ]),
        );
        taint_map.insert(
            "n",
            HashSet::from([
                "n".to_string(),
                "i".to_string(), // Since the update `i++` depends on the condition `i < n`.
                "left".to_string(),
                "right".to_string(),
            ]),
        );
        taint_map.insert("i", HashSet::from(["i".to_string(), "right".to_string()]));

        validate_taint(src, &taint_map);
    }

    fn validate_taint(src: &str, taint_map: &HashMap<&str, HashSet<String>>) {
        // Build CFG.
        let mut reports = ReportCollection::new();
        let cfg = parse_definition(src)
            .unwrap()
            .into_cfg(&Curve::default(), &mut reports)
            .unwrap()
            .into_ssa()
            .unwrap();
        assert!(reports.is_empty());

        let taint_analysis = run_taint_analysis(&cfg);
        for (source, expected_sinks) in taint_map {
            let source = VariableName::from_name(source).with_version(0);
            let sinks = taint_analysis
                .multi_step_taint(&source)
                .iter()
                .map(|var| var.name().to_string())
                .collect::<HashSet<_>>();
            assert_eq!(&sinks, expected_sinks);
        }
    }
}
