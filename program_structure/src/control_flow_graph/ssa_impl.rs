use log::{debug, error, trace};
use std::collections::HashSet;

use crate::environment::VarEnvironment;
use crate::ir::variable_meta::VariableMeta;
use crate::ir::*;
use crate::ssa::errors::*;
use crate::ssa::traits::*;

use super::basic_block::BasicBlock;
use super::param_data::ParameterData;

type Version = usize;

#[derive(Clone)]
pub struct VersionEnvironment {
    // Tracks the current scoped version of each variable. This is scoped to
    // ensure that versions are updated when a variable goes out of scope.
    scoped_versions: VarEnvironment<Version>,
    // Tracks the maximum version seen of each variable. This is not scoped to
    // ensure that we do not apply the same version to different occurrences of
    // the same variable names.
    global_versions: VarEnvironment<Version>,
    // Tracks defined signals to ensure that we know if a variable use represents
    // a variable, signal, or component.
    signals: HashSet<VariableName>,
    // Tracks defined components to ensure that we know if a variable use represents
    // a variable, signal, or component.
    components: HashSet<VariableName>,
}

impl VersionEnvironment {
    pub fn new() -> VersionEnvironment {
        VersionEnvironment {
            scoped_versions: VarEnvironment::new(),
            global_versions: VarEnvironment::new(),
            signals: HashSet::new(),
            components: HashSet::new(),
        }
    }

    // Get the current (scoped) version of the variable.
    pub fn get_current_version(&self, name: &VariableName) -> Option<Version> {
        let name = name.to_string_without_version();
        self.scoped_versions.get_variable(&name).cloned()
    }

    // Get the version to apply for a newly assigned variable.
    fn get_next_version(&mut self, name: &VariableName) -> Version {
        // Update the global version.
        let name = name.to_string_without_version();
        let version = match self.global_versions.get_variable(&name) {
            // The variable has not been seen before. This is version 0 of the variable.
            None => 0,
            // The variable has been seen before. The version needs to be increased by 1.
            Some(version) => version + 1,
        };
        self.global_versions.add_variable(&name, version);
        self.scoped_versions.add_variable(&name, version);
        version
    }

    fn add_signal(&mut self, name: &VariableName) {
        self.signals.insert(name.clone());
    }

    fn add_component(&mut self, name: &VariableName) {
        self.components.insert(name.clone());
    }

    fn has_signal(&self, name: &VariableName) -> bool {
        self.signals.contains(name)
    }

    fn has_component(&self, name: &VariableName) -> bool {
        self.signals.contains(name)
    }
}

impl From<&ParameterData> for VersionEnvironment {
    fn from(params: &ParameterData) -> VersionEnvironment {
        let mut env = VersionEnvironment::new();
        for name in params.iter() {
            env.get_next_version(name);
        }
        env
    }
}

impl SSAEnvironment for VersionEnvironment {
    // Enter variable scope.
    fn add_variable_block(&mut self) {
        self.scoped_versions.add_variable_block();
    }

    // Leave variable scope.
    fn remove_variable_block(&mut self) {
        self.scoped_versions.remove_variable_block();
    }
}

impl SSABasicBlock<VersionEnvironment> for BasicBlock {
    type Statement = Statement;

    fn insert_statement(&mut self, stmt: Statement) {
        self.prepend_statement(stmt);
    }

    fn get_statements<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Statement> + 'a> {
        Box::new(self.iter())
    }

    fn get_statements_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Statement> + 'a> {
        Box::new(self.iter_mut())
    }
}

impl SSAStatement<VersionEnvironment> for Statement {
    fn get_variables_written(&self) -> VariableSet {
        VariableMeta::get_variables_written(self)
            .iter()
            .map(ToString::to_string)
            .collect()
    }

    fn new_phi_statement(name: &str) -> Self {
        use AssignOp::*;
        use Expression::*;
        use Statement::*;
        let phi = Phi {
            meta: Meta::default(),
            // Phi expression arguments are added later.
            args: Vec::new(),
        };
        let mut stmt = Substitution {
            meta: Meta::default(),
            // Variable name is versioned lated.
            var: VariableName::name(name),
            op: AssignVar,
            rhe: phi,
            access: Vec::new(),
        };
        stmt.cache_variable_use();
        stmt
    }

    fn is_phi_statement(&self) -> bool {
        use Expression::*;
        use Statement::*;
        match self {
            Substitution {
                rhe: Phi { .. }, ..
            } => true,
            _ => false,
        }
    }

    fn is_phi_statement_for(&self, name: &str) -> bool {
        use Expression::*;
        use Statement::*;
        match self {
            Substitution {
                var,
                rhe: Phi { .. },
                ..
            } => var.to_string() == name,
            _ => false,
        }
    }

    fn ensure_phi_argument(&mut self, env: &VersionEnvironment) {
        use Expression::*;
        use Statement::*;
        match self {
            // If this is a phi statement we ensure that the RHS contains the
            // variable version from the given SSA environment.
            Substitution {
                var: name,
                rhe: Phi { args, .. },
                ..
            } => {
                trace!("phi statement for variable `{name}` found");
                if let Some(version) = env.get_current_version(name) {
                    // If the argument list does not contain the current version of the variable we add it.
                    if args.iter().any(|arg| {
                        matches!(
                            arg,
                            Variable { name, ..  } if name.get_version() == &Some(version)
                        )
                    }) {
                        return;
                    }
                    args.push(Variable {
                        meta: Meta::default(),
                        name: name.with_version(version),
                        access: Vec::new(),
                    });
                    self.cache_variable_use();
                }
            }
            // If this is not a phi statement we panic.
            _ => panic!("expected phi statement"),
        }
    }

    fn insert_ssa_variables(&mut self, env: &mut VersionEnvironment) -> SSAResult<()> {
        debug!("converting `{self}` to SSA");
        use Statement::*;
        let result = match self {
            IfThenElse { cond, .. } => visit_expression(cond, env),
            Return { value, .. } => visit_expression(value, env),
            Declaration { xtype, name, .. } => {
                assert!(name.get_version().is_none());
                use VariableType::*;
                *name = match xtype {
                    Var => {
                        // Since the CFG may contain loops, a declaration may not always
                        // be the first occurrence of a variable. If it is, the variable
                        // is only added to the environment on first use.
                        let version = env
                            .get_current_version(name)
                            .unwrap_or_default();
                        let versioned_name = name.with_version(version);
                        trace!(
                            "replacing (declared) variable `{name}` with SSA variable '{versioned_name}'"
                        );
                        versioned_name
                    }
                    Component => {
                        // Component names are not versioned.
                        env.add_component(name);
                        name.clone()
                    }
                    Signal(_, _) => {
                        // Signal names are not versioned.
                        env.add_signal(name);
                        name.clone()
                    }
                };
                Ok(())
            }
            Substitution { var, op, rhe, .. } => {
                assert!(var.get_version().is_none());
                // We need to visit the right-hand expression before updating the environment.
                visit_expression(rhe, env)?;
                *var = match op {
                    // If this is a variable assignment we need to version the variable.
                    AssignOp::AssignVar => {
                        // If this is the first assignment to the variable we set the version to 0,
                        // otherwise we increase the version by one.
                        let version = env.get_next_version(var);
                        let versioned_var = var.with_version(version);
                        trace!(
                            "replacing (written) variable `{var}` with SSA variable `{versioned_var}`"
                        );
                        versioned_var
                    }
                    // If this is a signal or component assignment we ignore it.
                    _ => var.clone(),
                };
                Ok(())
            }
            ConstraintEquality { lhe, rhe, .. } => {
                visit_expression(lhe, env)?;
                visit_expression(rhe, env)
            }
            LogCall { arg, .. } => visit_expression(arg, env),
            Assert { arg, .. } => visit_expression(arg, env),
        };
        // Since variables names may have changed we need to re-cache variable use.
        self.cache_variable_use();
        result
    }
}

/// Replaces each occurrence of the variable `v` with a versioned SSA variable `v.n`.
/// Currently, signals and components are not touched.
fn visit_expression(expr: &mut Expression, env: &VersionEnvironment) -> SSAResult<()> {
    use Expression::*;
    match expr {
        // Variables are decorated with the corresponding SSA version.
        Variable { meta, name, .. } => {
            assert!(
                name.get_version().is_none(),
                "variable already converted to SSA form"
            );
            // Ignore declared signals and components.
            if env.has_signal(name) || env.has_component(name) {
                return Ok(())
            }
            match env.get_current_version(name) {
                Some(version) => {
                    *name = name.with_version(version);
                    trace!(
                        "replacing (read) variable `{name}` with SSA variable `{name}.{version}`"
                    );
                    Ok(())
                }
                None => {
                    // TODO: Handle undeclared variables more gracefully.
                    error!("failed to convert undeclared variable `{name}` to SSA");
                    Err(SSAError::UndefinedVariableError {
                        name: name.to_string(),
                        file_id: meta.get_file_id(),
                        location: meta.file_location(),
                    })
                }
            }
        }
        // For all other expression types we simply recurse into their children.
        PrefixOp { rhe, .. } => visit_expression(rhe, env),
        InfixOp { lhe, rhe, .. } => {
            visit_expression(lhe, env)?;
            visit_expression(rhe, env)
        }
        InlineSwitchOp {
            cond,
            if_true,
            if_false,
            ..
        } => {
            visit_expression(cond, env)?;
            visit_expression(if_true, env)?;
            visit_expression(if_false, env)
        }
        Call { args, .. } => {
            for arg in args {
                visit_expression(arg, env)?;
            }
            Ok(())
        }
        ArrayInLine { values, .. } => {
            for value in values {
                visit_expression(value, env)?;
            }
            Ok(())
        }
        // phi expression arguments are updated in a later pass.
        Phi { .. } | Signal { .. } | Component { .. } | Number(_, _) => Ok(()),
    }
}
