use circom_algebra::modular_arithmetic;
use log::trace;
use std::collections::HashSet;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};

use crate::ast;
use crate::constants::UsefulConstants;

use super::declaration_map::VariableType;
use super::errors::{IRError, IRResult};
use super::ir::*;
use super::value_meta::{ValueEnvironment, ValueMeta, ValueReduction};
use super::variable_meta::{VariableMeta, VariableUse, VariableUses};

impl Expression {
    #[must_use]
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

    #[must_use]
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

    #[must_use]
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
        let mut variables_read = VariableUses::new();
        let mut signals_read = VariableUses::new();
        let mut components_read = VariableUses::new();

        use Expression::*;
        match self {
            InfixOp { lhe, rhe, .. } => {
                lhe.cache_variable_use();
                rhe.cache_variable_use();
                variables_read.extend(lhe.get_variables_read().iter().cloned());
                variables_read.extend(rhe.get_variables_read().iter().cloned());
                signals_read.extend(lhe.get_signals_read().iter().cloned());
                signals_read.extend(rhe.get_signals_read().iter().cloned());
                components_read.extend(lhe.get_components_read().iter().cloned());
                components_read.extend(rhe.get_components_read().iter().cloned());
            }
            PrefixOp { rhe, .. } => {
                rhe.cache_variable_use();
                variables_read.extend(rhe.get_variables_read().iter().cloned());
                signals_read.extend(rhe.get_signals_read().iter().cloned());
                components_read.extend(rhe.get_components_read().iter().cloned());
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
                variables_read.extend(cond.get_variables_read().clone());
                variables_read.extend(if_true.get_variables_read().clone());
                variables_read.extend(if_false.get_variables_read().clone());
                signals_read.extend(cond.get_signals_read().clone());
                signals_read.extend(if_true.get_signals_read().clone());
                signals_read.extend(if_false.get_signals_read().clone());
                components_read.extend(cond.get_components_read().clone());
                components_read.extend(if_true.get_components_read().clone());
                components_read.extend(if_false.get_components_read().clone());
            }
            Variable { meta, name, access } => {
                access.iter_mut().for_each(|access| {
                    if let Access::ArrayAccess(index) = access {
                        index.cache_variable_use();
                        variables_read.extend(index.get_variables_read().clone());
                        signals_read.extend(index.get_signals_read().clone());
                        components_read.extend(index.get_components_read().clone());
                    }
                });
                trace!("adding `{name}` to variables read");
                variables_read.insert(VariableUse::new(meta, name, access));
            }
            Signal { meta, name, access } => {
                access.iter_mut().for_each(|access| {
                    if let Access::ArrayAccess(index) = access {
                        index.cache_variable_use();
                        variables_read.extend(index.get_variables_read().clone());
                        signals_read.extend(index.get_signals_read().clone());
                        components_read.extend(index.get_components_read().clone());
                    }
                });
                trace!("adding `{name}` to signals read");
                signals_read.insert(VariableUse::new(meta, name, access));
            }
            Component { meta, name, access } => {
                access.iter_mut().for_each(|access| {
                    if let Access::ArrayAccess(index) = access {
                        index.cache_variable_use();
                        variables_read.extend(index.get_variables_read().clone());
                        signals_read.extend(index.get_signals_read().clone());
                        components_read.extend(index.get_components_read().clone());
                    }
                });
                trace!("adding `{name}` to components read");
                components_read.insert(VariableUse::new(meta, name, access));
            }
            Call { args, .. } => {
                args.iter_mut().for_each(|arg| {
                    arg.cache_variable_use();
                    variables_read.extend(arg.get_variables_read().clone());
                    signals_read.extend(arg.get_signals_read().clone());
                    components_read.extend(arg.get_components_read().clone());
                });
            }
            Phi { meta, args, .. } => {
                variables_read.extend(
                    args.iter()
                        .map(|name| VariableUse::new(meta, name, &Vec::new())),
                );
            }
            ArrayInLine { values, .. } => {
                values.iter_mut().for_each(|value| {
                    value.cache_variable_use();
                    variables_read.extend(value.get_variables_read().clone());
                    signals_read.extend(value.get_signals_read().clone());
                    components_read.extend(value.get_components_read().clone());
                });
            }
            Number(_, _) => {}
        }
        self.get_mut_meta()
            .get_variable_knowledge_mut()
            .set_variables_read(&variables_read)
            .set_variables_written(&VariableUses::new())
            .set_signals_read(&signals_read)
            .set_signals_written(&VariableUses::new())
            .set_components_read(&components_read)
            .set_components_written(&VariableUses::new());
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

impl ValueMeta for Expression {
    fn propagate_values(&mut self, env: &mut ValueEnvironment) -> bool {
        use Expression::*;
        use ValueReduction::*;
        match self {
            InfixOp {
                meta,
                lhe,
                infix_op,
                rhe,
                ..
            } => {
                let sub_result = lhe.propagate_values(env) | rhe.propagate_values(env);
                match infix_op.propagate_values(lhe.get_reduces_to(), rhe.get_reduces_to()) {
                    Some(value) => {
                        sub_result || meta.get_value_knowledge_mut().set_reduces_to(value)
                    }
                    None => sub_result,
                }
            }
            PrefixOp {
                meta,
                prefix_op,
                rhe,
            } => {
                let sub_result = rhe.propagate_values(env);
                match prefix_op.propagate_values(rhe.get_reduces_to()) {
                    Some(value) => {
                        sub_result || meta.get_value_knowledge_mut().set_reduces_to(value)
                    }
                    None => sub_result,
                }
            }
            InlineSwitchOp {
                meta,
                cond,
                if_true,
                if_false,
            } => {
                let sub_result = cond.propagate_values(env)
                    | if_true.propagate_values(env)
                    | if_false.propagate_values(env);
                match (
                    cond.get_reduces_to(),
                    if_true.get_reduces_to(),
                    if_false.get_reduces_to(),
                ) {
                    (
                        // The case true? value: _
                        Some(Boolean { value: cond }),
                        Some(value),
                        _,
                    ) if *cond => {
                        sub_result || meta.get_value_knowledge_mut().set_reduces_to(value.clone())
                    }
                    (
                        // The case false? _: value
                        Some(Boolean { value: cond }),
                        _,
                        Some(value),
                    ) if !cond => {
                        sub_result || meta.get_value_knowledge_mut().set_reduces_to(value.clone())
                    }
                    _ => sub_result,
                }
            }
            Variable {
                meta, name, access, ..
            } => {
                // TODO: Handle non-trivial variable accesses.
                if !access.is_empty() {
                    false
                } else if let Some(value) = env.get_variable(&name.to_string()) {
                    meta.get_value_knowledge_mut().set_reduces_to(value.clone())
                } else {
                    false
                }
            }
            Signal { .. } => {
                // TODO: Handle signal accesses.
                false
            }
            Component { .. } => {
                // TODO: Handle component accesses.
                false
            }
            Number(meta, value) => {
                let value = FieldElement {
                    value: value.clone(),
                };
                meta.get_value_knowledge_mut().set_reduces_to(value)
            }
            Call { args, .. } => {
                // TODO: Handle function calls.
                args.iter_mut().any(|arg| arg.propagate_values(env))
            }
            ArrayInLine { values, .. } => {
                // TODO: Handle inline arrays.
                values.iter_mut().any(|value| value.propagate_values(env))
            }
            Phi { meta, args, .. } => {
                // Only set the value of the phi expression if all arguments agree on the value.
                let values = args
                    .iter()
                    .map(|name| env.get_variable(&name.to_string()))
                    .collect::<Option<HashSet<_>>>();
                match values {
                    Some(values) if values.len() == 1 => {
                        // This unwrap is safe since the size is non-zero.
                        let value = *values.iter().next().unwrap();
                        meta.get_value_knowledge_mut().set_reduces_to(value.clone())
                    }
                    _ => false,
                }
            }
        }
    }

    fn is_constant(&self) -> bool {
        self.get_reduces_to().is_some()
    }

    fn is_boolean(&self) -> bool {
        matches!(self.get_reduces_to(), Some(ValueReduction::Boolean { .. }))
    }

    fn is_field_element(&self) -> bool {
        matches!(
            self.get_reduces_to(),
            Some(ValueReduction::FieldElement { .. })
        )
    }

    fn get_reduces_to(&self) -> Option<&ValueReduction> {
        self.get_meta().get_value_knowledge().get_reduces_to()
    }
}

impl ExpressionInfixOpcode {
    fn propagate_values(
        &self,
        lhv: Option<&ValueReduction>,
        rhv: Option<&ValueReduction>,
    ) -> Option<ValueReduction> {
        let constants = UsefulConstants::default();
        let p = constants.get_p();

        use ValueReduction::*;
        match (lhv, rhv) {
            // lhv and rhv reduce to two field elements.
            (Some(FieldElement { value: lhv }), Some(FieldElement { value: rhv })) => {
                use ExpressionInfixOpcode::*;
                match self {
                    Mul => {
                        let value = modular_arithmetic::mul(lhv, rhv, p);
                        Some(FieldElement { value })
                    }
                    Div => modular_arithmetic::div(lhv, rhv, p)
                        .ok()
                        .map(|value| FieldElement { value }),
                    Add => {
                        let value = modular_arithmetic::add(lhv, rhv, p);
                        Some(FieldElement { value })
                    }
                    Sub => {
                        let value = modular_arithmetic::sub(lhv, rhv, p);
                        Some(FieldElement { value })
                    }
                    Pow => {
                        let value = modular_arithmetic::pow(lhv, rhv, p);
                        Some(FieldElement { value })
                    }
                    IntDiv => modular_arithmetic::idiv(lhv, rhv, p)
                        .ok()
                        .map(|value| FieldElement { value }),
                    Mod => modular_arithmetic::mod_op(lhv, rhv, p)
                        .ok()
                        .map(|value| FieldElement { value }),
                    ShiftL => modular_arithmetic::shift_l(lhv, rhv, p)
                        .ok()
                        .map(|value| FieldElement { value }),
                    ShiftR => modular_arithmetic::shift_r(lhv, rhv, p)
                        .ok()
                        .map(|value| FieldElement { value }),
                    LesserEq => {
                        let value = modular_arithmetic::lesser_eq(lhv, rhv, p);
                        Some(Boolean {
                            value: modular_arithmetic::as_bool(&value, p),
                        })
                    }
                    GreaterEq => {
                        let value = modular_arithmetic::greater_eq(lhv, rhv, p);
                        Some(Boolean {
                            value: modular_arithmetic::as_bool(&value, p),
                        })
                    }
                    Lesser => {
                        let value = modular_arithmetic::lesser(lhv, rhv, p);
                        Some(Boolean {
                            value: modular_arithmetic::as_bool(&value, p),
                        })
                    }
                    Greater => {
                        let value = modular_arithmetic::greater(lhv, rhv, p);
                        Some(Boolean {
                            value: modular_arithmetic::as_bool(&value, p),
                        })
                    }
                    Eq => {
                        let value = modular_arithmetic::eq(lhv, rhv, p);
                        Some(Boolean {
                            value: modular_arithmetic::as_bool(&value, p),
                        })
                    }
                    NotEq => {
                        let value = modular_arithmetic::not_eq(lhv, rhv, p);
                        Some(Boolean {
                            value: modular_arithmetic::as_bool(&value, p),
                        })
                    }
                    BitOr => {
                        let value = modular_arithmetic::bit_or(lhv, rhv, p);
                        Some(FieldElement { value })
                    }
                    BitAnd => {
                        let value = modular_arithmetic::bit_and(lhv, rhv, p);
                        Some(FieldElement { value })
                    }
                    BitXor => {
                        let value = modular_arithmetic::bit_xor(lhv, rhv, p);
                        Some(FieldElement { value })
                    }
                    // Remaining operations do not make sense.
                    // TODO: Add report/error propagation here.
                    _ => None,
                }
            }
            // lhv and rhv reduce to two booleans.
            (Some(Boolean { value: lhv }), Some(Boolean { value: rhv })) => {
                use ExpressionInfixOpcode::*;
                match self {
                    BoolAnd => Some(Boolean {
                        value: *lhv && *rhv,
                    }),
                    BoolOr => Some(Boolean {
                        value: *lhv || *rhv,
                    }),
                    // Remaining operations do not make sense.
                    // TODO: Add report propagation here as well.
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

impl ExpressionPrefixOpcode {
    fn propagate_values(&self, rhe: Option<&ValueReduction>) -> Option<ValueReduction> {
        let constants = UsefulConstants::default();
        let p = constants.get_p();

        use ValueReduction::*;
        match rhe {
            // arg reduces to a field element.
            Some(FieldElement { value: arg }) => {
                use ExpressionPrefixOpcode::*;
                match self {
                    Sub => {
                        let value = modular_arithmetic::prefix_sub(arg, p);
                        Some(FieldElement { value })
                    }
                    Complement => {
                        let value = modular_arithmetic::complement_256(arg, p);
                        Some(FieldElement { value })
                    }
                    // Remaining operations do not make sense.
                    // TODO: Add report propagation here as well.
                    _ => None,
                }
            }
            // arg reduces to a boolean.
            Some(Boolean { value: arg }) => {
                use ExpressionPrefixOpcode::*;
                match self {
                    BoolNot => Some(Boolean { value: !arg }),
                    // Remaining operations do not make sense.
                    // TODO: Add report propagation here as well.
                    _ => None,
                }
            }
            None => None,
        }
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
                // Get the variable type from the corresponding declaration.
                // TODO: Generate a report rather than an error here.
                let xtype = env
                    .get_declaration(&name)
                    .map(|declaration| declaration.get_type())
                    .ok_or(IRError::UndefinedVariableError {
                        name: name.clone(),
                        file_id: meta.file_id,
                        file_location: meta.file_location(),
                    })?;

                use VariableType::*;
                match xtype {
                    Var => Ok(Expression::Variable {
                        meta: meta.into(),
                        name: name[..].into(),
                        access: access
                            .iter()
                            .map(|acc| acc.try_into_ir(env))
                            .collect::<IRResult<Vec<Access>>>()?,
                    }),
                    Component => Ok(Expression::Component {
                        meta: meta.into(),
                        name: name[..].into(),
                    }),
                    Signal(_, _) => Ok(Expression::Signal {
                        meta: meta.into(),
                        name: name[..].into(),
                        access: access
                            .iter()
                            .map(|acc| acc.try_into_ir(env))
                            .collect::<IRResult<Vec<Access>>>()?,
                    }),
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
            Variable { .. } => write!(f, "Expression::Variable"),
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
            Variable { name, .. } => write!(f, "{name}"),
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
            Phi { args, .. } => write!(f, "φ({})", vec_to_string(args)),
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

#[must_use]
fn vec_to_string<T: ToString>(args: &[T]) -> String {
    args.iter()
        .map(|arg| arg.to_string())
        .collect::<Vec<String>>()
        .join(", ")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_propagate_values() {
        use Expression::*;
        use ExpressionInfixOpcode::*;
        use ValueReduction::*;
        let mut lhe = Number(Meta::default(), 7u64.into());
        let mut rhe = Variable {
            meta: Meta::default(),
            name: VariableName::name("v"),
            access: Vec::new(),
        };
        let mut env = ValueEnvironment::new();
        env.add_variable("v", FieldElement { value: 3u64.into() });
        lhe.propagate_values(&mut env);
        rhe.propagate_values(&mut env);

        // Infix multiplication.
        let mut expr = InfixOp {
            meta: Meta::default(),
            infix_op: Mul,
            lhe: Box::new(lhe.clone()),
            rhe: Box::new(rhe.clone()),
        };
        expr.propagate_values(&mut env.clone());
        assert_eq!(
            expr.get_reduces_to(),
            Some(&FieldElement {
                value: 21u64.into()
            })
        );

        // Infix addition.
        let mut expr = InfixOp {
            meta: Meta::default(),
            infix_op: Add,
            lhe: Box::new(lhe.clone()),
            rhe: Box::new(rhe.clone()),
        };
        expr.propagate_values(&mut env.clone());
        assert_eq!(
            expr.get_reduces_to(),
            Some(&FieldElement {
                value: 10u64.into()
            })
        );

        // Infix integer division.
        let mut expr = InfixOp {
            meta: Meta::default(),
            infix_op: IntDiv,
            lhe: Box::new(lhe.clone()),
            rhe: Box::new(rhe.clone()),
        };
        expr.propagate_values(&mut env.clone());
        assert_eq!(
            expr.get_reduces_to(),
            Some(&FieldElement { value: 2u64.into() })
        );
    }
}
