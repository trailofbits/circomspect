use log::{debug, error, trace};
use std::ops::Range;

use crate::environment::VarEnvironment;
use crate::ir::declaration_map::{DeclarationMap, VariableType};
use crate::ir::variable_meta::VariableMeta;
use crate::ir::*;
use crate::ssa::errors::*;
use crate::ssa::traits::*;

use super::basic_block::BasicBlock;
use super::param_data::ParameterData;

type Version = usize;

#[derive(Clone)]
/// A type which tracks variable metadata relevant for SSA.
pub struct VersionEnvironment {
    /// Tracks the current scoped version of each variable. This is scoped to
    /// ensure that versions are updated when a variable goes out of scope.
    scoped_versions: VarEnvironment<Version>,
    /// Tracks the maximum version seen of each variable. This is not scoped to
    /// ensure that we do not apply the same version to different occurrences of
    /// the same variable names.
    global_versions: VarEnvironment<Version>,
    /// Tracks defined signals to ensure that we know if a variable use represents
    /// a variable, signal, or component.
    declarations: DeclarationMap,
}

impl VersionEnvironment {
    /// Returns a new environment initialized with the parameters of the template or function.
    pub fn new(parameters: &ParameterData, declarations: &DeclarationMap) -> VersionEnvironment {
        let mut env = VersionEnvironment {
            scoped_versions: VarEnvironment::new(),
            global_versions: VarEnvironment::new(),
            declarations: declarations.clone(),
        };
        for name in parameters.iter() {
            env.get_next_version(name);
        }
        env
    }

    /// Gets the current (scoped) version of the variable.
    pub fn get_current_version(&self, name: &VariableName) -> Option<Version> {
        let name = name.without_version().to_string();
        self.scoped_versions.get_variable(&name).cloned()
    }

    /// Gets the range of versions seen for the variable.
    pub fn get_version_range(&self, name: &VariableName) -> Option<Range<Version>> {
        let name = name.without_version().to_string();
        self.global_versions
            .get_variable(&name)
            .map(|max| 0..(max + 1))
    }

    /// Gets the version to apply for a newly assigned variable.
    fn get_next_version(&mut self, name: &VariableName) -> Version {
        // Update the global version.
        let name = name.without_version().to_string();
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

    /// Gets the dimensions of the given variable. We only version non-array variables.
    fn get_dimensions(&self, name: &VariableName) -> Option<&Vec<Expression>> {
        self.declarations.get_dimensions(name)
    }

    /// Returns true if the given name is a signal.
    fn has_signal(&self, name: &VariableName) -> bool {
        matches!(
            self.declarations.get_type(name),
            Some(VariableType::Signal(_, _))
        )
    }

    /// Returns true if the given name is a component.
    fn has_component(&self, name: &VariableName) -> bool {
        matches!(
            self.declarations.get_type(name),
            Some(VariableType::Component)
        )
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
            .map(|var_use| var_use.get_name().to_string())
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
        matches!(
            self,
            Substitution {
                rhe: Phi { .. },
                ..
            }
        )
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
                if let Some(env_version) = env.get_current_version(name) {
                    // If the argument list does not contain the current version of the variable we add it.
                    if args.iter().any(|arg|
                        matches!( arg.get_version(), &Some(arg_version) if arg_version == env_version)
                    ) {
                        return;
                    }
                    args.push(name.with_version(env_version));
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
            Substitution { var, op, rhe, .. } => {
                assert!(var.get_version().is_none());
                // We need to visit the right-hand expression before updating the environment.
                visit_expression(rhe, env)?;
                *var = match (op, env.get_dimensions(var)) {
                    // If this is a non-array variable assignment we need to version the variable.
                    (AssignOp::AssignVar, Some(dimensions)) if dimensions.is_empty() => {
                        // If this is the first assignment to the variable we set the version to 0,
                        // otherwise we increase the version by one.
                        let version = env.get_next_version(var);
                        let versioned_var = var.with_version(version);
                        trace!(
                            "replacing (written) variable `{var}` with SSA variable `{versioned_var}`"
                        );
                        versioned_var
                    }
                    // If this is an array, a signal or component assignment we ignore it.
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
                return Ok(());
            }
            // Ignore arrays.
            if let Some(dimensions) = env.get_dimensions(name) {
                if !dimensions.is_empty() {
                    return Ok(());
                }
            }
            match env.get_current_version(name) {
                Some(version) => {
                    trace!(
                        "replacing (read) variable `{name}` with SSA variable `{name}.{version}`"
                    );
                    *name = name.with_version(version);
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
