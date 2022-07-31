use log::trace;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};

use crate::ast;
use crate::ir::declaration_map::VariableType;

use super::errors::{IRError, IRResult};
use super::ir::*;
use super::value_meta::{ValueEnvironment, ValueMeta};
use super::variable_meta::{VariableMeta, VariableUse, VariableUses};

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
            AssignSignal => write!(f, "<--"),
            AssignConstraintSignal => write!(f, "<=="),
            AssignVar | AssignComponent => write!(f, "="),
        }
    }
}

impl VariableMeta for Statement {
    fn cache_variable_use(&mut self) {
        let mut variables_read = VariableUses::new();
        let mut variables_written = VariableUses::new();
        let mut signals_read = VariableUses::new();
        let mut signals_written = VariableUses::new();
        let mut components_read = VariableUses::new();
        let mut components_written = VariableUses::new();

        use Statement::*;
        match self {
            Substitution {
                meta,
                var,
                access,
                op,
                rhe,
            } => {
                rhe.cache_variable_use();
                variables_read.extend(rhe.get_variables_read().clone());
                signals_read.extend(rhe.get_signals_read().clone());
                components_read.extend(rhe.get_components_read().clone());
                access.iter_mut().for_each(|access| {
                    if let Access::ArrayAccess(index) = access {
                        index.cache_variable_use();
                        variables_read.extend(index.get_variables_read().clone());
                        signals_read.extend(index.get_signals_read().clone());
                        components_read.extend(index.get_components_read().clone());
                    }
                });
                match op {
                    AssignOp::AssignVar => {
                        trace!("adding `{var}` to variables written");
                        variables_written.insert(VariableUse::new(meta, var, access));
                    }
                    AssignOp::AssignComponent => {
                        trace!("adding `{var}` to components written");
                        components_written.insert(VariableUse::new(meta, var, access));
                    }
                    AssignOp::AssignSignal | AssignOp::AssignConstraintSignal => {
                        trace!("adding `{var}` to signals written");
                        signals_written.insert(VariableUse::new(meta, var, access));
                    }
                }
            }
            IfThenElse { cond, .. } => {
                cond.cache_variable_use();
                variables_read.extend(cond.get_variables_read().clone());
                signals_read.extend(cond.get_signals_read().clone());
                components_read.extend(cond.get_components_read().clone());
            }
            Return { value, .. } => {
                value.cache_variable_use();
                variables_read.extend(value.get_variables_read().clone());
                signals_read.extend(value.get_signals_read().clone());
                components_read.extend(value.get_components_read().clone());
            }
            LogCall { arg, .. } => {
                arg.cache_variable_use();
                variables_read.extend(arg.get_variables_read().clone());
                signals_read.extend(arg.get_signals_read().clone());
                components_read.extend(arg.get_components_read().clone());
            }
            Assert { arg, .. } => {
                arg.cache_variable_use();
                variables_read.extend(arg.get_variables_read().clone());
                signals_read.extend(arg.get_signals_read().clone());
                components_read.extend(arg.get_components_read().clone());
            }
            ConstraintEquality { lhe, rhe, .. } => {
                lhe.cache_variable_use();
                rhe.cache_variable_use();
                variables_read.extend(lhe.get_variables_read().iter().cloned());
                variables_read.extend(rhe.get_variables_read().iter().cloned());
                signals_read.extend(lhe.get_signals_read().iter().cloned());
                signals_read.extend(rhe.get_signals_read().iter().cloned());
                components_read.extend(lhe.get_components_read().iter().cloned());
                components_read.extend(rhe.get_components_read().iter().cloned());
            }
        }
        self.get_mut_meta()
            .get_variable_knowledge_mut()
            .set_variables_read(&variables_read)
            .set_variables_written(&variables_written)
            .set_signals_read(&signals_read)
            .set_signals_written(&signals_written)
            .set_components_read(&components_read)
            .set_components_written(&components_written);
    }

    fn get_variables_read(&self) -> &VariableUses {
        self.get_meta()
            .get_variable_knowledge()
            .get_variables_read()
    }

    fn get_variables_written(&self) -> &VariableUses {
        self.get_meta()
            .get_variable_knowledge()
            .get_variables_written()
    }

    fn get_signals_read(&self) -> &VariableUses {
        self.get_meta().get_variable_knowledge().get_signals_read()
    }

    fn get_signals_written(&self) -> &VariableUses {
        self.get_meta()
            .get_variable_knowledge()
            .get_signals_written()
    }

    fn get_components_read(&self) -> &VariableUses {
        self.get_meta()
            .get_variable_knowledge()
            .get_components_read()
    }

    fn get_components_written(&self) -> &VariableUses {
        self.get_meta()
            .get_variable_knowledge()
            .get_components_written()
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
            } => {
                // Since we distinguish component assignment from variable
                // assignment we use the variable type and AST operation to
                // determine the IR operation.
                let var_type = env
                    .get_declaration(var)
                    .map(|declaration| declaration.get_type());
                let op = match (var_type, op) {
                    (Some(VariableType::Var), _) => AssignOp::AssignVar,
                    (Some(VariableType::Component), ast::AssignOp::AssignVar) => {
                        AssignOp::AssignComponent
                    }
                    (_, ast::AssignOp::AssignConstraintSignal) => AssignOp::AssignConstraintSignal,
                    (_, ast::AssignOp::AssignSignal) => AssignOp::AssignSignal,
                    (_, ast::AssignOp::AssignVar) => AssignOp::AssignVar,
                };
                Ok(Statement::Substitution {
                    meta: meta.into(),
                    var: var[..].into(),
                    op,
                    rhe: rhe.try_into_ir(env)?,
                    access: access
                        .iter()
                        .map(|acc| acc.try_into_ir(env))
                        .collect::<IRResult<Vec<Access>>>()?,
                })
            }
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
