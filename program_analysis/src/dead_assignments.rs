use log::{debug, trace};
use std::collections::HashMap;
use std::fmt;

use program_structure::cfg::Cfg;
use program_structure::error_code::ReportCode;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::*;

pub struct DeadAssignmentWarning {
    name: String,
    file_id: Option<FileID>,
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
    name: String,
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl UnusedParameterWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            format!("The parameter `{}` is never read.", self.name),
            ReportCode::UnusedParameter,
        );
        if let Some(file_id) = self.file_id {
            report.add_primary(
                self.file_location,
                file_id,
                format!("The value of `{}` is never used.", self.name),
            );
        }
        report
    }
}

#[derive(Clone, PartialEq)]
enum VariableWrite {
    /// An oridnary write indicates a location where the variable is written to.
    OrdinaryWrite(Option<FileID>, FileLocation),
    /// A parameter write indicates that the variable is passed as a parameter
    /// to the function or template.
    Parameter(Option<FileID>, FileLocation),
}

impl fmt::Debug for VariableWrite {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            VariableWrite::OrdinaryWrite(_, file_location) => {
                write!(
                    f,
                    "variable assignment at {}-{}",
                    file_location.start, file_location.end
                )
            }
            VariableWrite::Parameter(_, file_location) => {
                write!(
                    f,
                    "parameter at {}-{}",
                    file_location.start, file_location.end
                )
            }
        }
    }
}

struct VariableWrites(HashMap<VariableName, VariableWrite>);

impl VariableWrites {
    pub fn new() -> VariableWrites {
        VariableWrites(HashMap::new())
    }

    /// Adds a variable write to the set.
    pub fn add_variable_written(&mut self, name: &VariableName, write: VariableWrite) {
        // This should always return `None` if we're running on SSA.
        assert_eq!(self.0.insert(name.clone(), write), None, "false");
    }

    /// Iterates over all parameter and variable assignments.
    pub fn iter(&self) -> impl Iterator<Item = (&VariableName, &VariableWrite)> {
        self.0.iter()
    }
}

#[derive(Clone, PartialEq)]
enum VariableRead {
    /// An ordinary read indicates a location where the variable is read in the
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

    /// Returns true if the variable is read outside a phi statement.
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

    /// Returns the variable names of phi statements where the given variable is
    /// in the list of phi function arguments.
    pub fn get_phi_statement_vars(&self, name: &VariableName) -> Vec<VariableName> {
        self.get_variable_reads(name)
            .iter()
            .filter_map(|read| self.get_phi_statement_var(read))
            .collect()
    }

    /// Returns true if the variable flows to an ordinary read.
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
pub fn find_dead_assignments(cfg: &Cfg) -> ReportCollection {
    debug!("running dead assignment analysis pass");
    // Collect all variable assignment locations.
    let mut variables_read = VariableReads::new();
    let mut variables_written = VariableWrites::new();
    for name in cfg.parameters().iter() {
        let file_id = cfg.parameters().file_id().clone();
        let file_location = cfg.parameters().file_location().clone();
        variables_written
            .add_variable_written(name, VariableWrite::Parameter(file_id, file_location));
    }
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            visit_statement(stmt, &mut variables_read, &mut variables_written);
        }
    }
    let mut reports = ReportCollection::new();
    for (name, write) in variables_written.iter() {
        if !variables_read.flows_to_ordinary_read(name) {
            reports.push(build_report(name.name(), write));
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
    trace!("visiting `{stmt}`");
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
                variables_read
                    .add_variable_read(arg, VariableRead::PhiStatement { var: var.clone() });
            }
        }
        Substitution { meta, var, rhe, .. } => {
            // If this is a variable assignment we add it to the variables written.
            if matches!(meta.type_knowledge().variable_type(), Some(VariableType::Local { .. })) {
                trace!("adding `{var}` to variables written");
                variables_written
                    .add_variable_written(var, VariableWrite::OrdinaryWrite(meta.file_id, meta.location.clone()));
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
        // Phi expressions are handled at the statement level since we need to
        // track the assigned variable.
        Phi { .. } => unreachable!("invalid expression type"),
        Access { var, access, .. } => {
            trace!("adding `{var}` to variables read");
            variables_read.add_variable_read(var, VariableRead::OrdinaryRead);
            for access in access {
                if let AccessType::ArrayAccess(index) = access {
                    visit_expression(index, variables_read);
                }
            }
        },
        Update { var, access, rhe, .. } => {
            trace!("adding `{var}` to variables read");
            variables_read.add_variable_read(var, VariableRead::OrdinaryRead);
            for access in access {
                if let AccessType::ArrayAccess(index) = access {
                    visit_expression(index, variables_read);
                }
            }
            visit_expression(rhe, variables_read);
        }
        Variable { name, .. } => {
            trace!("adding `{name}` to variables read");
            variables_read.add_variable_read(name, VariableRead::OrdinaryRead);
        }
        PrefixOp { rhe, .. } => {
            visit_expression(rhe, variables_read);
        }
        InfixOp { lhe, rhe, .. } => {
            visit_expression(lhe, variables_read);
            visit_expression(rhe, variables_read);
        }
        SwitchOp {
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
        Array { values, .. } => {
            for value in values {
                visit_expression(value, variables_read);
            }
        }
        Number(_, _) => (),
    }
}

fn build_report(name: &str, write: &VariableWrite) -> Report {
    use VariableWrite::*;
    match write {
        OrdinaryWrite(file_id, file_location) => DeadAssignmentWarning {
            name: name.to_string(),
            file_id: file_id.clone(),
            file_location: file_location.clone(),
        }
        .into_report(),
        Parameter(file_id, file_location) => UnusedParameterWarning {
            name: name.to_string(),
            file_id: file_id.clone(),
            file_location: file_location.clone(),
        }
        .into_report(),
    }
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::cfg::IntoCfg;

    use super::*;

    #[test]
    fn test_dead_assignments() {
        let src = r#"
            function f(x) {
                // a.0 = 0;
                var a = 0;
                if (x > 0) {
                    // a.1 = a.0 + 1;
                    a = a + 1;
                } else {
                    // a.2 = a.0 - 1;
                    a = a - 1;
                }
                // a.3 = phi(a.1, a.2);
                return x + 1;
            }
        "#;
        validate_reports(src, 2);

        let src = r#"
            function f(x) {
                // a.0 = 0;
                var a = 0;
                while (x > 0) {
                    // a.1 = a.0 + 1;
                    a = a + 1;
                    x = x - a;
                }
                // a.2 = phi(a.0, a.1);
                return x + 1;
            }
        "#;
        validate_reports(src, 0);

        let src = r#"
            function f(){
                var out[2];
                out[0] = g(0);
                out[1] = g(1);
                return out;
            }
        "#;
        validate_reports(src, 0);
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
        let reports = find_dead_assignments(&cfg);

        assert_eq!(reports.len(), expected_len);
    }
}
