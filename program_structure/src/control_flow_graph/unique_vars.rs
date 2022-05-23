use log::trace;
use std::convert::{TryFrom, TryInto};

use super::errors::{CFGError, CFGResult};
use super::param_data::ParameterData;

use crate::ast::{Expression, Meta, Statement};
use crate::environment::VarEnvironment;
use crate::error_definition::{Report, ReportCollection};
use crate::file_definition::{FileID, FileLocation};

type Version = usize;

// Location of the last seen declaration of a variable.
struct DeclarationData {
    file_id: FileID,
    file_location: FileLocation,
}

impl DeclarationData {
    fn new(file_id: FileID, file_location: FileLocation) -> DeclarationData {
        DeclarationData {
            file_id,
            file_location,
        }
    }

    fn get_file_id(&self) -> FileID {
        self.file_id
    }

    fn file_location(&self) -> FileLocation {
        self.file_location.clone()
    }
}

struct DeclarationEnvironment {
    // Tracks the last seen declaration of each variable. This is scoped to
    // ensure that we know when a new declaration shadows a previous declaration.
    declarations: VarEnvironment<DeclarationData>,
    // Tracks the current scoped version of each variable. This is scoped to
    // ensure that versions are updated when a variable goes out of scope.
    scoped_versions: VarEnvironment<Version>,
    // Tracks the maximum version seen of each variable. This is not scoped to
    // ensure that we do not apply the same version to different occurrences of
    // the same variable names. (See case 2 below.) If the variable is unique
    // the maximum version is `None` (i.e. the variable is not versioned).
    global_versions: VarEnvironment<Option<Version>>,
}

impl DeclarationEnvironment {
    pub fn new() -> DeclarationEnvironment {
        DeclarationEnvironment {
            declarations: VarEnvironment::new(),
            scoped_versions: VarEnvironment::new(),
            global_versions: VarEnvironment::new(),
        }
    }

    // Get the last declaration seen for the given variable.
    pub fn get_declaration(&self, name: &str) -> Option<&DeclarationData> {
        self.declarations.get_variable(name)
    }

    // Add a declaration for the given variable. Returns the version to apply for the declared variable.
    pub fn add_declaration(
        &mut self,
        name: &str,
        file_id: FileID,
        file_location: FileLocation,
    ) -> Option<Version> {
        self.declarations
            .add_variable(name, DeclarationData::new(file_id, file_location));
        self.get_next_version(name)
    }

    // Get the current (scoped) version of the variable.
    pub fn get_current_version(&self, name: &str) -> Option<&Version> {
        self.scoped_versions.get_variable(name)
    }

    // Get the version to apply for a newly declared variable.
    fn get_next_version(&mut self, name: &str) -> Option<Version> {
        // Update the global version.
        let version = match self.global_versions.get_variable(name) {
            // The variable is not seen before. It does not need to be versioned.
            None => None,
            // The variable has been seen exactly once. This declaration needs to be versioned.
            Some(None) => Some(0),
            // The variable has been seen more than once. The version needs to be increased by 1.
            Some(Some(version)) => Some(version + 1),
        };
        self.global_versions.add_variable(name, version);

        match version {
            // The variable does not need to be versioned. Do not update the scoped version.
            None => None,
            // The variable needs to be versioned. Update the scoped version.
            Some(version) => {
                self.scoped_versions.add_variable(name, version);
                Some(version)
            }
        }
    }

    // Enter variable scope.
    pub fn add_variable_block(&mut self) {
        self.declarations.add_variable_block();
        self.scoped_versions.add_variable_block();
    }

    // Leave variable scope.
    pub fn remove_variable_block(&mut self) {
        self.declarations.remove_variable_block();
        self.scoped_versions.remove_variable_block();
    }
}

impl TryFrom<&ParameterData> for DeclarationEnvironment {
    type Error = CFGError;

    fn try_from(param_data: &ParameterData) -> CFGResult<Self> {
        let mut env = DeclarationEnvironment::new();
        for name in param_data.iter() {
            let file_id = param_data.get_file_id();
            let file_location = param_data.get_location();
            if env
                .add_declaration(&name.to_string(), file_id, file_location.clone())
                .is_some()
            {
                return Err(CFGError::ParameterNameCollisionError {
                    name: name.to_string(),
                    file_id,
                    file_location,
                });
            }
        }
        Ok(env)
    }
}

/// Renames variables to ensure that variable names are globally unique.
///
/// There are a number of different cases to consider.
///
/// 1. The variable `x` has multiple declarations, where (at least) one
/// declaration of `x` shadows another declaration. E.g.
///
/// ```rs
/// function f(x) {
///     var y = 1;
///     if (x < y) {
///         var x = 3;
///         y = x;
///     }
/// }
/// ```
///
/// In this case, the inner declaration of the variable `x` shadows the outer
/// declaration and the second occurrence of `x` must be renamed.
///
/// 2. The variable `x` has multiple declarations but no declaration of `x`
/// shadows another declaration. E.g.
///
/// ```rs
/// function g(m) {
///     var n = 1;
///     if (m < n) {
///         var x = 1;
///         n = x;
///     } else {
///         var x = 2;
///         n = x;
///     }
/// }
///
/// In this case one of the declared variables still has to be renamed to ensure
/// global uniqueness.
///
/// 3. The variable `x` is only declared once. In this case the variable name is
/// already unique and `x` should not be renamed.
pub fn ensure_unique_variables(
    stmt: &mut Statement,
    param_data: &ParameterData,
) -> CFGResult<ReportCollection> {
    // Ensure that this method is only called on function or template bodies.
    assert!(matches!(stmt, Statement::Block { .. }));

    let mut env = param_data.try_into()?;
    let mut reports = ReportCollection::new();
    visit_statement(stmt, &mut env, &mut reports);
    Ok(reports)
}

fn visit_statement(
    stmt: &mut Statement,
    env: &mut DeclarationEnvironment,
    reports: &mut ReportCollection,
) {
    use Statement::*;
    match stmt {
        Declaration { name, meta, .. } => {
            trace!("visiting declared variable `{name}`");
            // If the current declaration shadows a previous declaration of the same
            // variable we generate a new report.
            if let Some(declaration) = env.get_declaration(name) {
                reports.push(build_report(name, &meta, declaration));
            }
            match env.add_declaration(name, meta.get_file_id(), meta.file_location()) {
                // This is a declaration of a previously unseen variable. It should not be versioned.
                None => {}
                // This is a declaration of a previously seen variable. It needs to be versioned.
                Some(version) => {
                    trace!("renaming declared shadowing variable `{name}` to `{name}.{version}`");
                    // It is a bit hacky to track the variable version as part of the variable name,
                    // but we do this in order to remain compatible with the original Circom AST.
                    *name = format!("{name}.{version}");
                }
            }
        }
        Substitution { var, rhe, .. } => {
            trace!("visiting assigned variable '{var}'");
            *var = match env.get_current_version(var) {
                Some(version) => {
                    trace!("renaming assigned shadowing variable `{var}` to `{var}.{version}`");
                    format!("{var}.{version}")
                }
                None => var.to_string(),
            };
            visit_expression(rhe, env);
        }
        Return { value, .. } => {
            visit_expression(value, env);
        }
        ConstraintEquality { lhe, rhe, .. } => {
            visit_expression(lhe, env);
            visit_expression(rhe, env);
        }
        LogCall { arg, .. } => {
            visit_expression(arg, env);
        }
        Assert { arg, .. } => {
            visit_expression(arg, env);
        }
        InitializationBlock {
            initializations, ..
        } => {
            for init in initializations {
                visit_statement(init, env, reports);
            }
        }
        While { cond, stmt, .. } => {
            visit_expression(cond, env);
            visit_statement(stmt, env, reports);
        }
        Block { stmts, .. } => {
            env.add_variable_block();
            for stmt in stmts {
                visit_statement(stmt, env, reports);
            }
            env.remove_variable_block();
        }
        IfThenElse {
            cond,
            if_case,
            else_case,
            ..
        } => {
            visit_expression(cond, env);
            visit_statement(if_case, env, reports);
            if let Some(else_case) = else_case {
                visit_statement(else_case, env, reports);
            }
        }
    }
}

fn visit_expression(expr: &mut Expression, env: &DeclarationEnvironment) {
    use Expression::*;
    match expr {
        Variable { name, .. } => {
            trace!("visiting variable '{name}'");
            *name = match env.get_current_version(name) {
                Some(version) => {
                    trace!(
                        "renaming occurrence of shadowing variable `{name}` to `{name}.{version}`"
                    );
                    format!("{name}.{version}")
                }
                None => name.clone(),
            };
        }
        InfixOp { lhe, rhe, .. } => {
            visit_expression(lhe, env);
            visit_expression(rhe, env);
        }
        PrefixOp { rhe, .. } => {
            visit_expression(rhe, env);
        }
        InlineSwitchOp {
            cond,
            if_true,
            if_false,
            ..
        } => {
            visit_expression(cond, env);
            visit_expression(if_true, env);
            visit_expression(if_false, env);
        }
        Number(_, _) => {}
        Call { args, .. } => {
            for arg in args {
                visit_expression(arg, env);
            }
        }
        ArrayInLine { values, .. } => {
            for value in values {
                visit_expression(value, env);
            }
        }
    }
}

fn build_report(name: &str, primary_meta: &Meta, secondary_decl: &DeclarationData) -> Report {
    CFGError::produce_report(CFGError::ShadowingVariableWarning {
        name: name.to_string(),
        primary_file_id: primary_meta.get_file_id(),
        primary_location: primary_meta.file_location(),
        secondary_file_id: secondary_decl.get_file_id(),
        secondary_location: secondary_decl.file_location(),
    })
}
