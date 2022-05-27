use log::debug;
use std::collections::HashMap;

use program_structure::cfg::Cfg;
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::*;

pub struct DeadAssignmentWarning {
    name: String,
    file_id: FileID,
    file_location: FileLocation,
}

impl DeadAssignmentWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            format!(
                "The variable `{}` is assigned a value, but this value is never read.",
                self.name
            ),
            ReportCode::DeadAssignment,
        );
        report.add_primary(
            self.file_location,
            self.file_id,
            "The value assigned here is never read.".to_string(),
        );
        report
    }
}

type VariableWrites = HashMap<VariableName, Meta>;

#[derive(Clone, PartialEq)]
enum VariableRead {
    /// An ordinary read indicated a location where the variable is read in the
    /// original program. All normal occurrences of the variable outside phi
    /// statements are ordinary reads.
    OrdinaryRead,
    /// Since phi statements are not part of the original program, we need to
    /// track these to see if the assigned variable is read somewhere else before
    /// declaring one of the phi function arguments as a dead variable.
    PhiStatement { var: VariableName },
}

struct VariableReads(HashMap<VariableName, Vec<VariableRead>>);

impl VariableReads {
    pub fn new() -> VariableReads {
        VariableReads(HashMap::new())
    }

    pub fn add_variable_read(&mut self, name: &VariableName, read: VariableRead) {
        match self.0.get_mut(name) {
            None => {
                self.0.insert(name.clone(), vec![read]);
            }
            Some(reads) => {
                reads.push(read);
            }
        }
    }

    fn get_variable_reads(&self, name: &VariableName) -> Vec<VariableRead> {
        // If the variable is not in the hash map it means that it is never read.
        self.0.get(name).cloned().unwrap_or_default()
    }

    // Returns true if the variable is read outside a phi statement.
    pub fn has_ordinary_read(&self, name: &VariableName) -> bool {
        self.get_variable_reads(name)
            .iter()
            .any(|read| matches!(read, VariableRead::OrdinaryRead))
    }

    fn get_phi_statement_var(&self, read: &VariableRead) -> Option<VariableName> {
        use VariableRead::*;
        match read {
            OrdinaryRead => None,
            PhiStatement { var } => Some(var.clone()),
        }
    }

    // Returns the variable names of phi statements where the given variable is
    // in the list of phi function arguments.
    pub fn get_phi_statement_vars(&self, name: &VariableName) -> Vec<VariableName> {
        self.get_variable_reads(name)
            .iter()
            .filter_map(|read| self.get_phi_statement_var(read))
            .collect()
    }

    // Returns true if the variable flows to an ordinary read.
    pub fn flows_to_ordinary_read(&self, name: &VariableName) -> bool {
        self.has_ordinary_read(name)
            || self
                .get_phi_statement_vars(name)
                .iter()
                .any(|var| self.flows_to_ordinary_read(var))
    }
}

/// Assignments to variables which are never read may indicate a logic error in
/// the code.
///
/// TODO: The current analysis does not catch variables which are part of the RHS
/// of a phi statement, where the LHS of the phi statement is never read.
pub fn find_dead_assignments(cfg: &Cfg) -> ReportCollection {
    debug!("running dead assignment analysis pass");
    // Collect all variable assignment locations.
    let mut variables_read = VariableReads::new();
    let mut variables_written = VariableWrites::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            visit_statement(stmt, &mut variables_read, &mut variables_written);
        }
    }
    let mut reports = ReportCollection::new();
    for (name, meta) in variables_written.iter() {
        // We assume that the CFG is converted to SSA here.
        if !variables_read.flows_to_ordinary_read(name) {
            reports.push(build_report(name.get_name(), meta));
        }
    }
    debug!("{} new reports generated", reports.len());
    reports
}

fn visit_statement(
    stmt: &Statement,
    variables_read: &mut VariableReads,
    variables_written: &mut VariableWrites,
) {
    use Expression::*;
    use Statement::*;
    match stmt {
        // Phi statements are tracked separately to make sure that we can do a
        // simple data flow analysis to see if a phi function argument flows to
        // a variable use in the original program.
        Substitution {
            var,
            rhe: Phi { args, .. },
            ..
        } => {
            for arg in args {
                match arg {
                    Variable { name, .. } => {
                        variables_read.add_variable_read(
                            name,
                            VariableRead::PhiStatement { var: var.clone() },
                        );
                    }
                    _ => unreachable!("invalid phi function argument"),
                }
            }
        }
        Substitution {
            meta, var, op, rhe, ..
        } => {
            // If this is a variable assignment we add it to the variables written.
            if matches!(op, AssignOp::AssignVar) {
                // Ensure that we are running this on SSA and that no variable is written multiple times.
                assert!(variables_written
                    .insert(var.clone(), meta.clone())
                    .is_none())
            }
            visit_expression(rhe, variables_read);
        }
        ConstraintEquality { lhe, rhe, .. } => {
            visit_expression(lhe, variables_read);
            visit_expression(rhe, variables_read);
        }
        IfThenElse { cond, .. } => visit_expression(cond, variables_read),
        Return { value, .. } => visit_expression(value, variables_read),
        LogCall { arg, .. } => visit_expression(arg, variables_read),
        Assert { arg, .. } => visit_expression(arg, variables_read),
    }
}

fn visit_expression(expr: &Expression, variables_read: &mut VariableReads) {
    use Expression::*;
    match expr {
        // Phi expressions are handled at the statement level since we need to track the assigned variable.
        Phi { .. } => unreachable!("invalid expression type"),
        Variable { name, .. } => {
            variables_read.add_variable_read(name, VariableRead::OrdinaryRead);
        }
        PrefixOp { rhe, .. } => {
            visit_expression(rhe, variables_read);
        }
        InfixOp { lhe, rhe, .. } => {
            visit_expression(lhe, variables_read);
            visit_expression(rhe, variables_read);
        }
        InlineSwitchOp {
            cond,
            if_true,
            if_false,
            ..
        } => {
            visit_expression(cond, variables_read);
            visit_expression(if_true, variables_read);
            visit_expression(if_false, variables_read);
        }
        Call { args, .. } => {
            for arg in args {
                visit_expression(arg, variables_read);
            }
        }

        ArrayInLine { values, .. } => {
            for value in values {
                visit_expression(value, variables_read);
            }
        }
        Component { .. } => (),
        Signal { .. } => (),
        Number(_, _) => (),
    }
}

fn build_report(name: &str, meta: &Meta) -> Report {
    DeadAssignmentWarning {
        name: name.to_string(),
        file_id: meta.get_file_id(),
        file_location: meta.file_location(),
    }
    .into_report()
}
