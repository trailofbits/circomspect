use log::{trace, debug};
use program_structure::cfg::parameters::Parameters;
use program_structure::intermediate_representation::Meta;
use std::collections::{HashMap, HashSet};

use program_structure::cfg::Cfg;
use program_structure::ir::{Expression, Statement, VariableName};
use program_structure::ir::variable_meta::{VariableMeta, VariableUse};

#[derive(Clone, Default)]
pub struct TaintAnalysis {
    taint_map: HashMap<VariableName, HashSet<VariableUse>>,
    definitions: HashMap<VariableName, VariableUse>,
}

impl TaintAnalysis {
    fn new(parameters: &Parameters) -> TaintAnalysis {
        // Add parameter definitions to taint analysis.
        let mut result = TaintAnalysis::default();
        let meta = Meta::new(
            parameters.file_location(),
            parameters.file_id()
        );
        for name in parameters.iter() {
            trace!("adding parameter declaration for `{name:?}`");
            let definition = VariableUse::new(
                &meta,
                name,
                &Vec::new()
            );
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
        //   component c[2] = C();
        //   c[0].in[0] <== 0;
        //   c[1].in[1] <== 1;
        //
        // As long as the initialized component flows to a constraint it will
        // not be flagged during side-effect analysis.
        self.definitions.insert(var.name().clone(), var.clone());
    }

    /// Get the variable use corresponding to the definition of the variable.
    pub fn definition(&self, var: &VariableName) -> Option<VariableUse> {
        self.definitions.get(var).cloned()
    }

    pub fn definitions(&self) -> impl Iterator<Item = &VariableUse> {
        self.definitions.values()
    }

    /// Add a single step taint from source to sink.
    fn add_taint_step(&mut self, source: &VariableName, sink: &VariableUse) {
        let sinks = self.taint_map.entry(source.clone()).or_default();
        sinks.insert(sink.clone());
    }

    /// Returns variables tainted in a single step by `source`.
    pub fn single_step_taint(&self, source: &VariableName) -> HashSet<VariableUse> {
        self.taint_map
            .get(source)
            .cloned()
            .unwrap_or_default()
    }

    /// Returns variables tainted in zero or more steps by `source`.
    pub fn multi_step_taint(&self, source: &VariableName) -> HashSet<VariableUse> {
        let mut result = HashSet::new();
        let mut update = match self.definition(source) {
            Some(var) => HashSet::from([var]),
            None => HashSet::default(),
        };
        while !update.is_subset(&result) {
            result.extend(update.iter().cloned());
            update = update
                .iter()
                .flat_map(|source| self.single_step_taint(source.name()))
                .collect();
        }
        result
    }

    pub fn taints_any(&self, source: &VariableName, sinks: &HashSet<VariableName>) -> bool {
        self.multi_step_taint(source).iter().any(|sink| sinks.contains(sink.name()))
    }
}

pub fn run_taint_analysis(cfg: &Cfg) -> TaintAnalysis {
    debug!("running taint analysis pass");
    let mut result = TaintAnalysis::new(cfg.parameters());

    use Statement::*;
    use Expression::*;
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            trace!("visiting statement `{stmt:?}`");
            // The first iterator will be non-empty for assignments only.
            for sink in stmt.variables_written() {
                if !matches!(stmt, Substitution { rhe: Phi { .. }, .. }) {
                    // Add the definition to the result.
                    trace!("adding variable declaration for `{:?}`", sink.name());
                    result.add_definition(sink);
                }
                for source in stmt.variables_read() {
                    // Add each taint step to the result.
                    result.add_taint_step(source.name(), &sink);
                }
            }
        }
    }
    result
}
