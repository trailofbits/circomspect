use std::fmt;
use std::fmt::{Debug, Display, Formatter};

use crate::ast;

use super::errors::{IRError, IRResult};
use super::ir::*;
use super::variable_meta::{VariableMeta, VariableSet};

impl Expression {
    pub fn get_meta(&self) -> &Meta {
        use Expression::*;
        match self {
            InfixOp { meta, .. }
            | PrefixOp { meta, .. }
            | InlineSwitchOp { meta, .. }
            | Variable { meta, .. }
            | Signal { meta, .. }
            | Component { meta, .. }
            | Number(meta, ..)
            | Call { meta, .. }
            | ArrayInLine { meta, .. }
            | Phi { meta, .. } => meta,
        }
    }
    pub fn get_mut_meta(&mut self) -> &mut Meta {
        use Expression::*;
        match self {
            InfixOp { meta, .. }
            | PrefixOp { meta, .. }
            | InlineSwitchOp { meta, .. }
            | Variable { meta, .. }
            | Signal { meta, .. }
            | Component { meta, .. }
            | Number(meta, ..)
            | Call { meta, .. }
            | ArrayInLine { meta, .. }
            | Phi { meta, .. } => meta,
        }
    }

    pub fn get_type(&self) -> ExpressionType {
        use Expression::*;
        match self {
            InfixOp { .. } => ExpressionType::InfixOp,
            PrefixOp { .. } => ExpressionType::PrefixOp,
            InlineSwitchOp { .. } => ExpressionType::InlineSwitchOp,
            Variable { .. } => ExpressionType::Variable,
            Signal { .. } => ExpressionType::Signal,
            Component { .. } => ExpressionType::Component,
            Number(_, _) => ExpressionType::Number,
            Call { .. } => ExpressionType::Call,
            ArrayInLine { .. } => ExpressionType::ArrayInLine,
            Phi { .. } => ExpressionType::Phi,
        }
    }
}

impl VariableMeta for Expression {
    fn cache_variable_use(&mut self) {
        let mut variables_read = VariableSet::new();

        use Expression::*;
        match self {
            InfixOp { lhe, rhe, .. } => {
                lhe.cache_variable_use();
                rhe.cache_variable_use();
                variables_read.extend(lhe.get_variables_read().iter().cloned());
                variables_read.extend(rhe.get_variables_read().iter().cloned());
            }
            PrefixOp { rhe, .. } => {
                rhe.cache_variable_use();
                variables_read.extend(rhe.get_variables_read().iter().cloned());
            }
            InlineSwitchOp {
                cond,
                if_true,
                if_false,
                ..
            } => {
                cond.cache_variable_use();
                if_true.cache_variable_use();
                if_false.cache_variable_use();
                variables_read.extend(cond.get_variables_read().iter().cloned());
                variables_read.extend(if_true.get_variables_read().iter().cloned());
                variables_read.extend(if_false.get_variables_read().iter().cloned());
            }
            Variable { .. } => {
                variables_read.insert(self.to_string());
            }
            Component { .. } | Signal { .. } | Number(_, _) => {}
            Call { args, .. } => {
                args.iter_mut().for_each(|arg| {
                    arg.cache_variable_use();
                    variables_read.extend(arg.get_variables_read().iter().cloned());
                });
            }
            Phi { args, .. } => {
                args.iter_mut().for_each(|arg| {
                    arg.cache_variable_use();
                    variables_read.extend(arg.get_variables_read().iter().cloned());
                });
            }
            ArrayInLine { values, .. } => {
                values.iter_mut().for_each(|value| {
                    value.cache_variable_use();
                    variables_read.extend(value.get_variables_read().iter().cloned());
                });
            }
        }
        self.get_mut_meta()
            .get_mut_variable_knowledge()
            .set_variables_read(&variables_read);
        self.get_mut_meta()
            .get_mut_variable_knowledge()
            .set_variables_written(&VariableSet::new());
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

// Attempt to convert an AST expression to an IR expression. This will currently
// fail with an `anyhow::Error` for undeclared variables.
impl TryIntoIR for ast::Expression {
    type IR = Expression;
    type Error = IRError;

    fn try_into_ir(&self, env: &mut IREnvironment) -> IRResult<Self::IR> {
        use ast::Expression::*;
        match self {
            InfixOp {
                meta,
                lhe,
                infix_op,
                rhe,
            } => Ok(Expression::InfixOp {
                meta: meta.into(),
                lhe: Box::new(lhe.as_ref().try_into_ir(env)?),
                infix_op: infix_op.into(),
                rhe: Box::new(rhe.as_ref().try_into_ir(env)?),
            }),
            PrefixOp {
                meta,
                prefix_op,
                rhe,
            } => Ok(Expression::PrefixOp {
                meta: meta.into(),
                prefix_op: prefix_op.into(),
                rhe: Box::new(rhe.as_ref().try_into_ir(env)?),
            }),
            InlineSwitchOp {
                meta,
                cond,
                if_true,
                if_false,
            } => Ok(Expression::InlineSwitchOp {
                meta: meta.into(),
                cond: Box::new(cond.as_ref().try_into_ir(env)?),
                if_true: Box::new(if_true.as_ref().try_into_ir(env)?),
                if_false: Box::new(if_false.as_ref().try_into_ir(env)?),
            }),
            Variable { meta, name, access } => {
                if env.has_variable(name) {
                    Ok(Expression::Variable {
                        meta: meta.into(),
                        name: name.into(),
                        version: None,
                        access: access
                            .iter()
                            .map(|acc| acc.try_into_ir(env))
                            .collect::<IRResult<Vec<Access>>>()?,
                    })
                } else if env.has_component(name) {
                    Ok(Expression::Component {
                        meta: meta.into(),
                        name: name.clone(),
                    })
                } else if env.has_signal(name) {
                    Ok(Expression::Signal {
                        meta: meta.into(),
                        name: name.clone(),
                        access: access
                            .iter()
                            .map(|acc| acc.try_into_ir(env))
                            .collect::<IRResult<Vec<Access>>>()?,
                    })
                } else {
                    Err(IRError::UndefinedVariableError {
                        name: name.to_string(),
                        file_id: meta.get_file_id(),
                        file_location: meta.file_location(),
                    })
                }
            }
            Number(meta, value) => Ok(Expression::Number(meta.into(), value.clone())),
            Call { meta, id, args } => Ok(Expression::Call {
                meta: meta.into(),
                id: id.clone(),
                args: args
                    .iter()
                    .map(|arg| arg.try_into_ir(env))
                    .collect::<IRResult<Vec<Expression>>>()?,
            }),
            ArrayInLine { meta, values } => Ok(Expression::ArrayInLine {
                meta: meta.into(),
                values: values
                    .iter()
                    .map(|arg| arg.try_into_ir(env))
                    .collect::<IRResult<Vec<Expression>>>()?,
            }),
        }
    }
}

// Attempt to convert an AST access to an IR access. This will currently
// fail with an `anyhow::Error` for undeclared variables.
impl TryIntoIR for ast::Access {
    type IR = Access;
    type Error = IRError;

    fn try_into_ir(&self, env: &mut IREnvironment) -> IRResult<Self::IR> {
        use ast::Access::*;
        match self {
            ArrayAccess(e) => Ok(Access::ArrayAccess(e.try_into_ir(env)?)),
            ComponentAccess(s) => Ok(Access::ComponentAccess(s.clone())),
        }
    }
}

impl Debug for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use Expression::*;
        match self {
            Number(_, _) => write!(f, "Expression::Number"),
            Signal { .. } => write!(f, "Expression::Signal"),
            Component { .. } => write!(f, "Expression::Component"),
            Variable { version: None, .. } => write!(f, "Expression::Variable"),
            Variable {
                version: Some(_), ..
            } => write!(f, "Expression::SSAVariable"),
            InfixOp { .. } => write!(f, "Expression::InfixOp"),
            PrefixOp { .. } => write!(f, "Expression::PrefixOp"),
            InlineSwitchOp { .. } => write!(f, "Expression::InlineSwitchOp"),
            Call { .. } => write!(f, "Expression::Call"),
            ArrayInLine { .. } => write!(f, "Expression::ArrayInline"),
            Phi { .. } => write!(f, "Expression::Phi"),
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use Expression::*;
        match self {
            Number(_, value) => write!(f, "{}", value),
            Signal { name, .. } => write!(f, "{name}"),
            Component { name, .. } => write!(f, "{name}"),
            Variable {
                name,
                version: None,
                ..
            } => write!(f, "{name}"),
            Variable {
                name,
                version: Some(version),
                ..
            } => {
                write!(f, "{name}.{version}")
            }
            InfixOp {
                lhe, infix_op, rhe, ..
            } => write!(f, "({} {} {})", lhe, infix_op, rhe),
            PrefixOp { prefix_op, rhe, .. } => write!(f, "{}({})", prefix_op, rhe),
            InlineSwitchOp {
                cond,
                if_true,
                if_false,
                ..
            } => write!(f, "({}?{}:{})", cond, if_true, if_false),
            Call { id, args, .. } => write!(f, "{}({})", id, vec_to_string(args)),
            ArrayInLine { values, .. } => write!(f, "[{}]", vec_to_string(values)),
            Phi { args, .. } => write!(f, "φ({})", vec_to_string(&args)),
        }
    }
}

impl Display for ExpressionInfixOpcode {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use ExpressionInfixOpcode::*;
        match self {
            Mul => f.write_str("*"),
            Div => f.write_str("/"),
            Add => f.write_str("+"),
            Sub => f.write_str("-"),
            Pow => f.write_str("**"),
            IntDiv => f.write_str("\\"),
            Mod => f.write_str("%"),
            ShiftL => f.write_str("<<"),
            ShiftR => f.write_str(">>"),
            LesserEq => f.write_str("<="),
            GreaterEq => f.write_str(">="),
            Lesser => f.write_str("<"),
            Greater => f.write_str(">"),
            Eq => f.write_str("=="),
            NotEq => f.write_str("!="),
            BoolOr => f.write_str("||"),
            BoolAnd => f.write_str("&&"),
            BitOr => f.write_str("|"),
            BitAnd => f.write_str("&"),
            BitXor => f.write_str("^"),
        }
    }
}

impl Display for ExpressionPrefixOpcode {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        use ExpressionPrefixOpcode::*;
        match self {
            Sub => f.write_str("-"),
            BoolNot => f.write_str("!"),
            Complement => f.write_str("~"),
        }
    }
}

fn vec_to_string(elems: &Vec<Expression>) -> String {
    elems
        .iter()
        .map(|arg| arg.to_string())
        .collect::<Vec<String>>()
        .join(", ")
}
