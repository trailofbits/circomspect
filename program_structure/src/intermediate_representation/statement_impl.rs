use log::trace;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};

use crate::ast;

use super::errors::{IRError, IRResult};
use super::ir::*;
use super::variable_meta::{VariableMeta, VariableSet};

impl Statement {
    #[must_use]
    pub fn get_meta(&self) -> &Meta {
        use Statement::*;
        match self {
            IfThenElse { meta, .. }
            | Return { meta, .. }
            | Declaration { meta, .. }
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
            | Declaration { meta, .. }
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
            Declaration { .. } => StatementType::Declaration,
            Substitution { .. } => StatementType::Substitution,
            LogCall { .. } => StatementType::LogCall,
            Assert { .. } => StatementType::Assert,
            ConstraintEquality { .. } => StatementType::ConstraintEquality,
        }
    }
}

impl Debug for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use Statement::*;
        match self {
            IfThenElse { .. } => write!(f, "IR::IfThenElse"),
            Return { .. } => write!(f, "IR::Return"),
            Declaration { .. } => write!(f, "IR::Declaration"),
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
            Declaration { xtype, name, .. } => write!(f, "{xtype} {name}"),
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

impl Display for VariableType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use VariableType::*;
        match self {
            Var => write!(f, "var"),
            Signal(signal_type, _) => write!(f, "signal {signal_type}"),
            Component => write!(f, "component"),
        }
    }
}

impl Display for SignalType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use SignalType::*;
        match self {
            Input => write!(f, "input"),
            Output => write!(f, "output"),
            Intermediate => Ok(()), // Intermediate signals have no explicit signal type.
        }
    }
}

impl VariableMeta for Statement {
    fn cache_variable_use(&mut self) {
        let mut variables_read = VariableSet::new();
        let mut variables_written = VariableSet::new();

        use Statement::*;
        match self {
            IfThenElse { cond, .. } => {
                cond.cache_variable_use();
                variables_read.extend(cond.get_variables_read().iter().cloned());
            }
            Return { value, .. } => {
                value.cache_variable_use();
                variables_read.extend(value.get_variables_read().iter().cloned());
            }
            Declaration { .. } => {
                // A variable declaration is not considered a use.
            }
            Substitution { var, op, rhe, .. } => {
                rhe.cache_variable_use();
                variables_read.extend(rhe.get_variables_read().iter().cloned());
                if matches!(op, AssignOp::AssignVar) {
                    trace!("adding {var} to variables written");
                    variables_written.insert(var.clone());
                }
            }
            LogCall { arg, .. } => {
                arg.cache_variable_use();
                variables_read.extend(arg.get_variables_read().iter().cloned());
            }
            Assert { arg, .. } => {
                arg.cache_variable_use();
                variables_read.extend(arg.get_variables_read().iter().cloned());
            }
            ConstraintEquality { lhe, rhe, .. } => {
                lhe.cache_variable_use();
                rhe.cache_variable_use();
                variables_read.extend(lhe.get_variables_read().iter().cloned());
                variables_read.extend(rhe.get_variables_read().iter().cloned());
            }
        }
        self.get_mut_meta()
            .get_mut_variable_knowledge()
            .set_variables_read(&variables_read);
        self.get_mut_meta()
            .get_mut_variable_knowledge()
            .set_variables_written(&variables_written);
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
}

// Attempt to convert an AST statement into an IR statement. This will fail on
// statements that need to be handled manually (`While` and `IfThenElse`), as
// well as statements that have no direct IR counterparts (like `Block` and
// `InitializationBlock`). It will also fail if it encounters an undeclared
// variable.
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
            Declaration {
                meta,
                xtype,
                name,
                is_constant,
                dimensions,
            } => {
                use ast::SignalType::*;
                use ast::VariableType::*;
                match xtype {
                    Var => env.add_variable(name, ()),
                    Component => env.add_component(name, ()),
                    Signal(Input, _) => env.add_input(name, ()),
                    Signal(Output, _) => env.add_output(name, ()),
                    Signal(Intermediate, _) => env.add_intermediate(name, ()),
                };
                Ok(Statement::Declaration {
                    meta: meta.into(),
                    xtype: xtype.into(),
                    name: name.into(),
                    is_constant: is_constant.clone(),
                    dimensions: dimensions
                        .iter()
                        .map(|xt| xt.try_into_ir(env))
                        .collect::<IRResult<Vec<Expression>>>()?,
                })
            }
            Substitution {
                meta,
                var,
                op,
                rhe,
                access,
            } => Ok(Statement::Substitution {
                meta: meta.into(),
                var: var.into(),
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
            IfThenElse { .. } | While { .. } => {
                unreachable!("failed to convert AST statement to IR")
            }
            InitializationBlock { .. } | Block { .. } => {
                unreachable!("failed to convert AST statement to IR")
            }
        }
    }
}
