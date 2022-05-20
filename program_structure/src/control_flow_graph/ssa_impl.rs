use log::trace;
use std::collections::{HashMap, HashSet};

use crate::ir::variable_meta::VariableMeta;
use crate::ir::*;
use crate::ssa::errors::{SSAError, SSAResult};
use crate::ssa::traits::{SSABasicBlock, SSAEnvironment, SSAStatement, VariableSet};

use super::basic_block::BasicBlock;
use super::param_data::ParameterData;

type Version = usize;

#[derive(Clone)]
pub struct VersionEnvironment {
    variables: HashMap<String, Version>,
    signals: HashSet<String>,
    components: HashSet<String>,
}

impl VersionEnvironment {
    pub fn new() -> VersionEnvironment {
        VersionEnvironment {
            variables: HashMap::new(),
            signals: HashSet::new(),
            components: HashSet::new(),
        }
    }
}

impl From<&ParameterData> for VersionEnvironment {
    fn from(params: &ParameterData) -> VersionEnvironment {
        let mut env = VersionEnvironment::new();
        for name in params.iter() {
            env.add_variable(&name.to_string(), Version::default())
        }
        env
    }
}

impl SSAEnvironment for VersionEnvironment {
    fn add_variable(&mut self, name: &str, version: Version) {
        trace!("adding {name} version from environment: {version:?}");
        self.variables.insert(name.to_string(), version);
    }

    fn add_signal(&mut self, name: &str) {
        self.signals.insert(name.to_string());
    }

    fn add_component(&mut self, name: &str) {
        self.components.insert(name.to_string());
    }

    fn has_variable(&self, name: &str) -> bool {
        self.variables.contains_key(name)
    }

    fn has_signal(&self, name: &str) -> bool {
        self.signals.contains(name)
    }

    fn has_component(&self, name: &str) -> bool {
        self.signals.contains(name)
    }

    fn get_variable(&self, name: &str) -> Option<Version> {
        trace!(
            "getting {name} version from environment: {:?}",
            self.variables.get(name)
        );
        self.variables.get(name).cloned()
    }
}

impl SSABasicBlock for BasicBlock {
    type Statement = Statement;

    fn insert_statement(&mut self, stmt: Self::Statement) {
        self.prepend_statement(stmt);
    }

    fn get_statements<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Statement> + 'a> {
        Box::new(self.iter())
    }

    fn get_statements_mut<'a>(&'a mut self) -> Box<dyn Iterator<Item = &'a mut Statement> + 'a> {
        Box::new(self.iter_mut())
    }
}

impl SSAStatement for Statement {
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
            // phi expression arguments are added later.
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

    fn ensure_phi_argument(&mut self, env: &impl SSAEnvironment) {
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
                let unversioned_name = name.without_version();
                trace!("phi statement for variable '{name}' found");
                if let Some(version) = env.get_variable(&unversioned_name.to_string()) {
                    // If the argument list does not contain the current version of the variable we add it.
                    if args.iter().any(|arg| {
                        matches!(
                            arg,
                            Variable { name, ..  } if *name.get_version() == Some(version)
                        )
                    }) {
                        return;
                    }
                    args.push(Variable {
                        meta: Meta::default(),
                        name: unversioned_name.with_version(version),
                        access: Vec::new(),
                    });
                    self.cache_variable_use();
                }
            }
            // If this is not a phi statement we panic.
            _ => panic!("expected phi statement"),
        }
    }

    fn insert_ssa_variables(&mut self, env: &mut impl SSAEnvironment) -> SSAResult<()> {
        trace!("converting '{self}' to SSA");
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
                            .get_variable(&name.to_string_without_version())
                            .unwrap_or_default();
                        let versioned_name = name.with_version(version);
                        trace!(
                            "replacing (declared) variable '{name}' with SSA variable '{versioned_name}'"
                        );
                        versioned_name
                    }
                    Component => {
                        // Component names are not versioned.
                        env.add_component(&name.to_string());
                        name.clone()
                    }
                    Signal(_, _) => {
                        // Signal names are not versioned.
                        env.add_signal(&name.to_string());
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
                        let version = env
                            .get_variable(&var.to_string_without_version())
                            .map(|version| version + 1)
                            .unwrap_or_default();
                        env.add_variable(&var.to_string(), version);
                        let versioned_var = var.with_version(version);

                        trace!(
                            "replacing (written) variable '{var}' with SSA variable '{versioned_var}'"
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
fn visit_expression(expr: &mut Expression, env: &impl SSAEnvironment) -> SSAResult<()> {
    use Expression::*;
    match expr {
        // Variables are decorated with the corresponding SSA version.
        Variable { meta, name, .. } => {
            assert!(
                name.get_version().is_none(),
                "variable already converted to SSA form"
            );
            match env.get_variable(&name.to_string_without_version()) {
                Some(version) => {
                    *name = name.with_version(version);
                    trace!(
                        "replacing (read) variable '{name}' with SSA variable '{name}.{version}'"
                    );
                    Ok(())
                }
                None => {
                    trace!("failed to convert undeclared variable '{name}' to SSA");
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
