use log::trace;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};

use crate::ast;

use super::errors::{IRError, IRResult};
use super::ir::*;
use super::value_meta::{ValueEnvironment, ValueMeta};
use super::variable_meta::{VariableMeta, VariableSet};

impl Statement {
    #[must_use]
    pub fn get_meta(&self) -> &Meta {
        use Statement::*;
        match self {
            IfThenElse { meta, .. }
            | Return { meta, .. }
            | Substitution { meta, .. }
            | LogCall { meta, .. }
            | Assert { meta, .. }
            | ConstraintEquality { meta, .. } => meta,
        }
    }

    #[must_use]
    pub fn get_mut_meta(&mut self) -> &mut Meta {
        use Statement::*;
        match self {
            IfThenElse { meta, .. }
            | Return { meta, .. }
            | Substitution { meta, .. }
            | LogCall { meta, .. }
            | Assert { meta, .. }
            | ConstraintEquality { meta, .. } => meta,
        }
    }

    #[must_use]
    pub fn get_type(&self) -> StatementType {
        use Statement::*;
        match self {
            IfThenElse { .. } => StatementType::IfThenElse,
            Return { .. } => StatementType::Return,
            Substitution { .. } => StatementType::Substitution,
            LogCall { .. } => StatementType::LogCall,
            Assert { .. } => StatementType::Assert,
            ConstraintEquality { .. } => StatementType::ConstraintEquality,
        }
    }
}

impl Statement {
    pub fn propagate_values(&mut self, env: &mut ValueEnvironment) -> bool {
        use Statement::*;
        match self {
            IfThenElse { cond, .. } => cond.propagate_values(env),
            Return { value, .. } => value.propagate_values(env),
            Substitution {
                var, access, rhe, ..
            } => {
                // TODO: Handle non-trivial variable accesses.
                if rhe.propagate_values(env) && access.is_empty() {
                    match rhe.get_reduces_to() {
                        Some(value) => env.add_variable(&var.to_string(), value.clone()),
                        None => (),
                    }
                    true
                } else {
                    false
                }
            }
            ConstraintEquality { lhe, rhe, .. } => {
                lhe.propagate_values(env) | rhe.propagate_values(env)
            }
            LogCall { arg, .. } => arg.propagate_values(env),
            Assert { arg, .. } => arg.propagate_values(env),
        }
    }
}

impl Debug for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use Statement::*;
        match self {
            IfThenElse { .. } => write!(f, "IR::IfThenElse"),
            Return { .. } => write!(f, "IR::Return"),
            Substitution { .. } => write!(f, "IR::Substitution"),
            LogCall { .. } => write!(f, "IR::LogCall"),
            Assert { .. } => write!(f, "IR::Assert"),
            ConstraintEquality { .. } => write!(f, "IR::ConstraintEquality"),
        }
    }
}

impl<'a> Display for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use Statement::*;
        match self {
            IfThenElse { cond, .. } => write!(f, "if {cond}"),
            Return { value, .. } => write!(f, "return {value}"),
            Substitution { var, op, rhe, .. } => write!(f, "{var} {op} {rhe}"),
            LogCall { arg, .. } => write!(f, "log({arg})"),
            Assert { arg, .. } => write!(f, "assert({arg})"),
            ConstraintEquality { lhe, rhe, .. } => write!(f, "{lhe} === {rhe}"),
        }
    }
}

impl Display for AssignOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use AssignOp::*;
        match self {
            AssignVar => write!(f, "="),
            AssignSignal => write!(f, "<--"),
            AssignConstraintSignal => write!(f, "<=="),
        }
    }
}

impl VariableMeta for Statement {
    fn cache_variable_use(&mut self) {
        let mut variables_read = VariableSet::new();
        let mut variables_written = VariableSet::new();
        let mut signals_read = VariableSet::new();
        let mut signals_written = VariableSet::new();

        use Statement::*;
        match self {
            IfThenElse { cond, .. } => {
                cond.cache_variable_use();
                variables_read.extend(cond.get_variables_read().clone());
                signals_read.extend(cond.get_signals_read().clone());
            }
            Return { value, .. } => {
                value.cache_variable_use();
                variables_read.extend(value.get_variables_read().clone());
                signals_read.extend(value.get_signals_read().clone());
            }
            Substitution { var, op, rhe, .. } => {
                rhe.cache_variable_use();
                variables_read.extend(rhe.get_variables_read().clone());
                signals_read.extend(rhe.get_signals_read().clone());
                match op {
                    AssignOp::AssignVar => {
                        trace!("adding `{var}` to variables written");
                        variables_written.insert(var.clone());
                    }
                    AssignOp::AssignSignal => {
                        trace!("adding `{var}` to signals written");
                        signals_written.insert(var.clone());
                    }
                    AssignOp::AssignConstraintSignal => {
                        trace!("adding `{var}` to signals written");
                        signals_written.insert(var.clone());
                    }
                }
            }
            LogCall { arg, .. } => {
                arg.cache_variable_use();
                variables_read.extend(arg.get_variables_read().clone());
                signals_read.extend(arg.get_signals_read().clone());
            }
            Assert { arg, .. } => {
                arg.cache_variable_use();
                variables_read.extend(arg.get_variables_read().clone());
                signals_read.extend(arg.get_signals_read().clone());
            }
            ConstraintEquality { lhe, rhe, .. } => {
                lhe.cache_variable_use();
                rhe.cache_variable_use();
                variables_read.extend(lhe.get_variables_read().clone());
                variables_read.extend(rhe.get_variables_read().clone());
                signals_read.extend(lhe.get_signals_read().clone());
                signals_read.extend(rhe.get_signals_read().clone());
            }
        }
        self.get_mut_meta()
            .get_variable_knowledge_mut()
            .set_variables_read(&variables_read)
            .set_variables_written(&variables_written)
            .set_signals_read(&signals_read)
            .set_signals_written(&signals_written);
    }

    fn get_variables_read(&self) -> &VariableSet {
        self.get_meta()
            .get_variable_knowledge()
            .get_variables_read()
    }
    fn get_variables_written(&self) -> &VariableSet {
        self.get_meta()
            .get_variable_knowledge()
            .get_variables_written()
    }

    fn get_signals_read(&self) -> &VariableSet {
        self.get_meta().get_variable_knowledge().get_signals_read()
    }
    fn get_signals_written(&self) -> &VariableSet {
        self.get_meta()
            .get_variable_knowledge()
            .get_signals_written()
    }
}

// Attempt to convert an AST statement into an IR statement. This will fail on
// statements that need to be handled manually (`While` and `IfThenElse`), as
// well as statements that have no direct IR counterparts (like `Declaration`,
// `Block` and `InitializationBlock`). It will also fail if it encounters an
// undeclared variable.
impl TryIntoIR for ast::Statement {
    type IR = Statement;
    type Error = IRError;

    fn try_into_ir(&self, env: &mut IREnvironment) -> IRResult<Self::IR> {
        use ast::Statement::*;
        match self {
            Return { meta, value } => Ok(Statement::Return {
                meta: meta.into(),
                value: value.try_into_ir(env)?,
            }),
            Substitution {
                meta,
                var,
                op,
                rhe,
                access,
            } => Ok(Statement::Substitution {
                meta: meta.into(),
                var: var[..].into(),
                op: op.into(),
                rhe: rhe.try_into_ir(env)?,
                access: access
                    .iter()
                    .map(|acc| acc.try_into_ir(env))
                    .collect::<IRResult<Vec<Access>>>()?,
            }),
            ConstraintEquality { meta, lhe, rhe } => Ok(Statement::ConstraintEquality {
                meta: meta.into(),
                lhe: lhe.try_into_ir(env)?,
                rhe: rhe.try_into_ir(env)?,
            }),
            LogCall { meta, arg } => Ok(Statement::LogCall {
                meta: meta.into(),
                arg: arg.try_into_ir(env)?,
            }),
            Assert { meta, arg } => Ok(Statement::Assert {
                meta: meta.into(),
                arg: arg.try_into_ir(env)?,
            }),
            Declaration { .. } => {
                unreachable!("failed to convert AST statement to IR")
            }
            IfThenElse { .. } | While { .. } => {
                unreachable!("failed to convert AST statement to IR")
            }
            InitializationBlock { .. } | Block { .. } => {
                unreachable!("failed to convert AST statement to IR")
            }
        }
    }
}
