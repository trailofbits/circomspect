use log::{debug, trace, warn};
use std::collections::HashSet;
use std::convert::TryInto;
use std::ops::Range;

use crate::environment::VarEnvironment;
use crate::ir::declarations::{Declaration, Declarations};
use crate::ir::variable_meta::VariableMeta;
use crate::ir::*;
use crate::ssa::errors::*;
use crate::ssa::traits::*;

use super::basic_block::BasicBlock;
use super::parameters::Parameters;

type Version = usize;

pub struct Config {}

impl SSAConfig for Config {
    type Version = Version;
    type Variable = VariableName;
    type Environment = Environment;
    type Statement = Statement;
    type BasicBlock = BasicBlock;
}

#[derive(Clone)]
/// A type which tracks variable metadata relevant for SSA.
pub struct Environment {
    /// Tracks the current scoped version of each variable. This is scoped to
    /// ensure that versions are updated when a variable goes out of scope.
    scoped_versions: VarEnvironment<Version>,
    /// Tracks the maximum version seen of each variable. This is not scoped to
    /// ensure that we do not apply the same version to different occurrences of
    /// the same variable names.
    global_versions: VarEnvironment<Version>,
    /// Tracks declared local variables, components, and signals to ensure that
    /// we know if a variable use represents a variable, signal, or component.
    declarations: Declarations,
}

impl Environment {
    /// Returns a new environment initialized with the parameters of the template or function.
    pub fn new(parameters: &Parameters, declarations: &Declarations) -> Environment {
        let mut env = Environment {
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
        // Need to use format to include the suffix.
        let name = format!("{:?}", name.without_version());
        self.scoped_versions.get_variable(&name).cloned()
    }

    /// Gets the range of versions seen for the variable.
    pub fn get_version_range(&self, name: &VariableName) -> Option<Range<Version>> {
        // Need to use format to include the suffix.
        let name = format!("{:?}", name.without_version());
        self.global_versions
            .get_variable(&name)
            .map(|max| 0..(max + 1))
    }

    /// Gets the version to apply for a newly assigned variable.
    fn get_next_version(&mut self, name: &VariableName) -> Version {
        // Need to use format to include the suffix.
        let name = format!("{:?}", name.without_version());
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

    /// Returns true if the given name is a local variable.
    fn is_local(&self, name: &VariableName) -> bool {
        matches!(self.declarations.get_type(name), Some(VariableType::Local))
    }
}

impl SSAEnvironment for Environment {
    // Enter variable scope.
    fn add_variable_scope(&mut self) {
        self.scoped_versions.add_variable_block();
    }

    // Leave variable scope.
    fn remove_variable_scope(&mut self) {
        self.scoped_versions.remove_variable_block();
    }
}

impl SSABasicBlock<Config> for BasicBlock {
    fn prepend_statement(&mut self, stmt: Statement) {
        self.prepend_statement(stmt);
    }

    fn statements<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Statement> + 'a> {
        Box::new(self.iter())
    }

    fn statements_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Statement> + 'a> {
        Box::new(self.iter_mut())
    }
}

impl SSAStatement<Config> for Statement {
    fn variables_written(&self) -> HashSet<VariableName> {
        VariableMeta::locals_written(self)
            .iter()
            .map(|var_use| var_use.name())
            .cloned()
            .collect()
    }

    fn new_phi_statement(name: &VariableName, env: &Environment) -> Self {
        use AssignOp::*;
        use Expression::*;
        use Statement::*;
        let phi = Phi {
            // We have no location for this statement.
            meta: Meta::default(),
            // Phi expression arguments are added later.
            args: Vec::new(),
        };
        let mut stmt = Substitution {
            meta: Meta::default(),
            // Variable name is versioned later.
            var: name.without_version(),
            op: AssignLocalOrComponent,
            rhe: phi,
        };
        // We need to update the node metadata to have a current view of
        // variable use.
        stmt.propagate_types(&env.declarations);
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

    fn is_phi_statement_for(&self, name: &VariableName) -> bool {
        use Expression::*;
        use Statement::*;
        match self {
            Substitution {
                var,
                rhe: Phi { .. },
                ..
            } => var == name,
            _ => false,
        }
    }

    fn ensure_phi_argument(&mut self, env: &Environment) {
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
                // If the environment knows about the variable, we ensure that
                // the versioned variable occurs as an argument to the RHS.
                if let Some(env_version) = env.get_current_version(name) {
                    // If the argument list does not contain the current version of the variable we add it.
                    if args.iter().any(|arg|
                        matches!( arg.version(), &Some(arg_version) if arg_version == env_version)
                    ) {
                        return;
                    }
                    args.push(name.with_version(env_version));
                    self.propagate_types(&env.declarations);
                    self.cache_variable_use();
                }
            }
            // If this is not a phi statement we panic.
            _ => panic!("expected phi statement"),
        }
    }

    fn insert_ssa_variables(&mut self, env: &mut Environment) -> SSAResult<()> {
        debug!("converting `{self}` to SSA");
        use Statement::*;
        let result = match self {
            Declaration { dimensions, .. } => {
                // Since at this point we still don't know the version range for
                // the declared variable we treat declarations in a later pass.
                for size in dimensions {
                    visit_expression(size, env)?;
                }
                Ok(())
            }
            Substitution { var, rhe, .. } => {
                assert!(var.version().is_none());
                visit_expression(rhe, env)?;
                // If this is a variable assignment we need to version the variable.
                // TODO: We should maybe treat undeclared variables as local variables.
                if env.is_local(var) {
                    // If this is the first assignment to the variable we set the version to 0,
                    // otherwise we increase the version by one.
                    let version = env.get_next_version(var);
                    trace!(
                        "replacing (written) variable `{var}` with SSA variable `{var}.{version}`"
                    );
                    *var = var.with_version(version);
                }
                Ok(())
            }
            ConstraintEquality { lhe, rhe, .. } => {
                visit_expression(lhe, env)?;
                visit_expression(rhe, env)
            }
            IfThenElse { cond, .. } => visit_expression(cond, env),
            Return { value, .. } => visit_expression(value, env),
            LogCall { arg, .. } => visit_expression(arg, env),
            Assert { arg, .. } => visit_expression(arg, env),
        };
        // We need to update the node metadata to have a current view of
        // variable use.
        self.propagate_types(&env.declarations);
        self.cache_variable_use();
        result
    }
}

/// Replaces each occurrence of the variable `v` with a versioned SSA variable `v.n`.
/// Signals and components are not touched.
fn visit_expression(expr: &mut Expression, env: &mut Environment) -> SSAResult<()> {
    use Expression::*;
    match expr {
        // Variables are updated with the corresponding SSA version.
        Variable { meta, name, .. } => {
            assert!(
                name.version().is_none(),
                "variable already converted to SSA form"
            );
            // Ignore declared signals and components, and undeclared variables.
            // TODO: We should maybe treat undeclared variables as local variables.
            if !env.is_local(name) {
                return Ok(());
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
                    warn!("failed to convert undeclared variable `{name}` to SSA");
                    Err(SSAError::UndefinedVariableError {
                        name: name.to_string(),
                        file_id: meta.file_id(),
                        location: meta.file_location(),
                    })
                }
            }
        }
        // Local array accesses are updated with the corresponding SSA version.
        Access { meta, var, access } => {
            for access in access {
                if let AccessType::ArrayAccess(index) = access {
                    visit_expression(index, env)?;
                }
            }
            // Ignore declared signals and components, and undeclared variables.
            if !env.is_local(var) {
                return Ok(());
            }
            assert!(
                var.version().is_none(),
                "variable already converted to SSA form"
            );
            match env.get_current_version(var) {
                Some(version) => {
                    trace!("replacing (read) variable `{var}` with SSA variable `{var}.{version}`");
                    *var = var.with_version(version);
                    Ok(())
                }
                None => {
                    // TODO: Handle undeclared variables more gracefully.
                    warn!("failed to convert undeclared variable `{var}` to SSA");
                    Err(SSAError::UndefinedVariableError {
                        name: var.to_string(),
                        file_id: meta.file_id(),
                        location: meta.file_location(),
                    })
                }
            }
        }
        Update {
            var, access, rhe, ..
        } => {
            visit_expression(rhe, env)?;
            for access in access {
                if let AccessType::ArrayAccess(index) = access {
                    visit_expression(index, env)?;
                }
            }
            // Ignore declared signals and components, and undeclared variables.
            if !env.is_local(var) {
                return Ok(());
            }
            assert!(
                var.version().is_none(),
                "variable already converted to SSA form"
            );
            match env.get_current_version(var) {
                Some(version) => {
                    trace!("replacing (read) variable `{var}` with SSA variable `{var}.{version}`");
                    *var = var.with_version(version);
                    Ok(())
                }
                None => {
                    // This is the first assignment to an array. Add the
                    // variable to the environment and get the first version.
                    let version = env.get_next_version(var);
                    trace!("replacing (read) variable `{var}` with SSA variable `{var}.{version}`");
                    *var = var.with_version(version);
                    Ok(())
                }
            }
        }
        // For all other expression types we simply recurse into their children.
        PrefixOp { rhe, .. } => visit_expression(rhe, env),
        InfixOp { lhe, rhe, .. } => {
            visit_expression(lhe, env)?;
            visit_expression(rhe, env)
        }
        SwitchOp {
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
        Array { values, .. } => {
            for value in values {
                visit_expression(value, env)?;
            }
            Ok(())
        }
        // phi expression arguments are updated in a later pass.
        Phi { .. } | Number(_, _) => Ok(()),
    }
}

/// Add each version of each variable to the corresponding declaration statement.
/// Returns a `Declarations` structure containing all declared variables in the
/// CFG.
#[must_use]
pub fn update_declarations(
    basic_blocks: &mut Vec<BasicBlock>,
    parameters: &Parameters,
    env: &Environment,
) -> Declarations {
    let mut versioned_declarations = Declarations::new();
    for name in parameters.iter() {
        // Since parameters are not considered immutable we must assume that
        // they may be updated (and hence occur as different versions)
        // throughout the function/template.
        for version in env
            .get_version_range(name)
            .expect("variable in environment")
        {
            trace!(
                "adding declaration for variable `{}`",
                name.with_version(version)
            );
            versioned_declarations.add_declaration(&Declaration::new(
                &name.with_version(version),
                &VariableType::Local,
                parameters.file_id(),
                parameters.file_location(),
            ));
        }
    }
    for basic_block in basic_blocks {
        for stmt in basic_block.iter_mut() {
            if let Statement::Declaration {
                meta,
                names,
                var_type,
                ..
            } = stmt
            {
                let name = names.first();
                assert!(names.len() == 1 && name.version().is_none());

                if matches!(var_type, VariableType::Local) {
                    if env.get_version_range(name).is_none() {
                        println!("unknown variable `{name}`");
                    }
                    let mut versions = env
                        .get_version_range(name)
                        .unwrap_or(0..1) // This will happen if the variable is not assigned to.
                        .collect::<Vec<_>>();
                    versions.sort_unstable();

                    // Add a new declaration for each version of the local variable.
                    let mut versioned_names = Vec::new();
                    for version in versions {
                        trace!(
                            "adding declaration for variable `{}`",
                            name.with_version(version)
                        );
                        versioned_names.push(name.with_version(version));
                        versioned_declarations.add_declaration(&Declaration::new(
                            &name.with_version(version),
                            var_type,
                            &meta.file_id(),
                            &meta.file_location(),
                        ));
                    }
                    // Update declaration statement with versioned variable names.
                    *names = versioned_names.try_into().expect("variable in environment");
                } else {
                    // Declarations of signals and components are just copied over.
                    trace!("adding declaration for variable `{}`", names.first());
                    versioned_declarations.add_declaration(&Declaration::new(
                        name,
                        var_type,
                        &meta.file_id(),
                        &meta.file_location(),
                    ));
                }
            }
        }
    }
    versioned_declarations
}
