use circom_algebra::modular_arithmetic;
use log::trace;
use num_traits::Zero;
use std::collections::HashSet;
use std::fmt;

use crate::constants::UsefulConstants;

use super::declarations::Declarations;
use super::ir::*;
use super::type_meta::TypeMeta;
use super::value_meta::{ValueEnvironment, ValueMeta, ValueReduction};
use super::variable_meta::{VariableMeta, VariableUse, VariableUses};

impl Expression {
    #[must_use]
    pub fn meta(&self) -> &Meta {
        use Expression::*;
        match self {
            InfixOp { meta, .. }
            | PrefixOp { meta, .. }
            | SwitchOp { meta, .. }
            | Variable { meta, .. }
            | Number(meta, ..)
            | Call { meta, .. }
            | Array { meta, .. }
            | Update { meta, .. }
            | Access { meta, .. }
            | Phi { meta, .. } => meta,
        }
    }

    #[must_use]
    pub fn meta_mut(&mut self) -> &mut Meta {
        use Expression::*;
        match self {
            InfixOp { meta, .. }
            | PrefixOp { meta, .. }
            | SwitchOp { meta, .. }
            | Variable { meta, .. }
            | Number(meta, ..)
            | Call { meta, .. }
            | Array { meta, .. }
            | Update { meta, .. }
            | Access { meta, .. }
            | Phi { meta, .. } => meta,
        }
    }
}

/// Syntactic equality for expressions.
impl PartialEq for Expression {
    fn eq(&self, other: &Expression) -> bool {
        use Expression::*;
        match (self, other) {
            (
                InfixOp {
                    lhe: self_lhe,
                    infix_op: self_op,
                    rhe: self_rhe,
                    ..
                },
                InfixOp {
                    lhe: other_lhe,
                    infix_op: other_op,
                    rhe: other_rhe,
                    ..
                },
            ) => self_op == other_op && self_lhe == other_lhe && self_rhe == other_rhe,
            (
                PrefixOp {
                    prefix_op: self_op,
                    rhe: self_rhe,
                    ..
                },
                PrefixOp {
                    prefix_op: other_op,
                    rhe: other_rhe,
                    ..
                },
            ) => self_op == other_op && self_rhe == other_rhe,
            (
                SwitchOp {
                    cond: self_cond,
                    if_true: self_true,
                    if_false: self_false,
                    ..
                },
                SwitchOp {
                    cond: other_cond,
                    if_true: other_true,
                    if_false: other_false,
                    ..
                },
            ) => self_cond == other_cond && self_true == other_true && self_false == other_false,
            (
                Variable {
                    name: self_name, ..
                },
                Variable {
                    name: other_name, ..
                },
            ) => self_name == other_name,
            (Number(_, self_value), Number(_, other_value)) => self_value == other_value,
            (
                Call {
                    name: self_id,
                    args: self_args,
                    ..
                },
                Call {
                    name: other_id,
                    args: other_args,
                    ..
                },
            ) => self_id == other_id && self_args == other_args,
            (
                Array {
                    values: self_values,
                    ..
                },
                Array {
                    values: other_values,
                    ..
                },
            ) => self_values == other_values,
            (
                Update {
                    var: self_var,
                    access: self_access,
                    rhe: self_rhe,
                    ..
                },
                Update {
                    var: other_var,
                    access: other_access,
                    rhe: other_rhe,
                    ..
                },
            ) => self_var == other_var && self_access == other_access && self_rhe == other_rhe,
            (
                Access {
                    var: self_var,
                    access: self_access,
                    ..
                },
                Access {
                    var: other_var,
                    access: other_access,
                    ..
                },
            ) => self_var == other_var && self_access == other_access,
            (
                Phi {
                    args: self_args, ..
                },
                Phi {
                    args: other_args, ..
                },
            ) => self_args == other_args,
            _ => false,
        }
    }
}

impl Eq for Expression {}

impl TypeMeta for Expression {
    fn propagate_types(&mut self, vars: &Declarations) {
        use Expression::*;
        match self {
            InfixOp { lhe, rhe, .. } => {
                lhe.propagate_types(vars);
                rhe.propagate_types(vars);
            }
            PrefixOp { rhe, .. } => {
                rhe.propagate_types(vars);
            }
            SwitchOp {
                cond,
                if_true,
                if_false,
                ..
            } => {
                cond.propagate_types(vars);
                if_true.propagate_types(vars);
                if_false.propagate_types(vars);
            }
            Variable { meta, name } => {
                if let Some(var_type) = vars.get_type(name) {
                    meta.type_knowledge_mut().set_variable_type(var_type);
                }
            }
            Call { args, .. } => {
                for arg in args {
                    arg.propagate_types(vars);
                }
            }
            Array { values, .. } => {
                for value in values {
                    value.propagate_types(vars);
                }
            }
            Access { meta, var, access } => {
                for access in access.iter_mut() {
                    if let AccessType::ArrayAccess(index) = access {
                        index.propagate_types(vars);
                    }
                }
                if let Some(var_type) = vars.get_type(var) {
                    meta.type_knowledge_mut().set_variable_type(var_type);
                }
            }
            Update {
                meta,
                var,
                access,
                rhe,
                ..
            } => {
                rhe.propagate_types(vars);
                for access in access.iter_mut() {
                    if let AccessType::ArrayAccess(index) = access {
                        index.propagate_types(vars);
                    }
                }
                if let Some(var_type) = vars.get_type(var) {
                    meta.type_knowledge_mut().set_variable_type(var_type);
                }
            }
            Phi { .. } => {
                // All phi node arguments are local variables.
            }
            Number(_, _) => {}
        }
    }

    fn is_local(&self) -> bool {
        self.meta().type_knowledge().is_local()
    }

    fn is_signal(&self) -> bool {
        self.meta().type_knowledge().is_signal()
    }

    fn is_component(&self) -> bool {
        self.meta().type_knowledge().is_component()
    }

    fn variable_type(&self) -> Option<&VariableType> {
        self.meta().type_knowledge().variable_type()
    }
}

impl VariableMeta for Expression {
    fn cache_variable_use(&mut self) {
        let mut locals_read = VariableUses::new();
        let mut signals_read = VariableUses::new();
        let mut components_read = VariableUses::new();

        use Expression::*;
        match self {
            InfixOp { lhe, rhe, .. } => {
                lhe.cache_variable_use();
                rhe.cache_variable_use();
                locals_read.extend(lhe.locals_read().iter().cloned());
                locals_read.extend(rhe.locals_read().iter().cloned());
                signals_read.extend(lhe.signals_read().iter().cloned());
                signals_read.extend(rhe.signals_read().iter().cloned());
                components_read.extend(lhe.components_read().iter().cloned());
                components_read.extend(rhe.components_read().iter().cloned());
            }
            PrefixOp { rhe, .. } => {
                rhe.cache_variable_use();
                locals_read.extend(rhe.locals_read().iter().cloned());
                signals_read.extend(rhe.signals_read().iter().cloned());
                components_read.extend(rhe.components_read().iter().cloned());
            }
            SwitchOp {
                cond,
                if_true,
                if_false,
                ..
            } => {
                cond.cache_variable_use();
                if_true.cache_variable_use();
                if_false.cache_variable_use();
                locals_read.extend(cond.locals_read().clone());
                locals_read.extend(if_true.locals_read().clone());
                locals_read.extend(if_false.locals_read().clone());
                signals_read.extend(cond.signals_read().clone());
                signals_read.extend(if_true.signals_read().clone());
                signals_read.extend(if_false.signals_read().clone());
                components_read.extend(cond.components_read().clone());
                components_read.extend(if_true.components_read().clone());
                components_read.extend(if_false.components_read().clone());
            }
            Variable { meta, name } => {
                match meta.type_knowledge().variable_type() {
                    Some(VariableType::Local { .. }) => {
                        trace!("adding `{name}` to local variables read");
                        locals_read.insert(VariableUse::new(meta, name, &Vec::new()));
                    }
                    Some(VariableType::Component { .. }) => {
                        trace!("adding `{name}` to components read");
                        components_read.insert(VariableUse::new(meta, name, &Vec::new()));
                    }
                    Some(VariableType::Signal { .. }) => {
                        trace!("adding `{name}` to signals read");
                        signals_read.insert(VariableUse::new(meta, name, &Vec::new()));
                    }
                    None => {
                        // If the variable type is unknown we ignore it.
                        trace!("variable `{name}` of unknown type read");
                    }
                }
            }
            Call { args, .. } => {
                args.iter_mut().for_each(|arg| {
                    arg.cache_variable_use();
                    locals_read.extend(arg.locals_read().clone());
                    signals_read.extend(arg.signals_read().clone());
                    components_read.extend(arg.components_read().clone());
                });
            }
            Phi { meta, args, .. } => {
                locals_read.extend(
                    args.iter()
                        .map(|name| VariableUse::new(meta, name, &Vec::new())),
                );
            }
            Array { values, .. } => {
                values.iter_mut().for_each(|value| {
                    value.cache_variable_use();
                    locals_read.extend(value.locals_read().clone());
                    signals_read.extend(value.signals_read().clone());
                    components_read.extend(value.components_read().clone());
                });
            }
            Access { meta, var, access } => {
                // Cache array index variable use.
                for access in access.iter_mut() {
                    if let AccessType::ArrayAccess(index) = access {
                        index.cache_variable_use();
                        locals_read.extend(index.locals_read().clone());
                        signals_read.extend(index.signals_read().clone());
                        components_read.extend(index.components_read().clone());
                    }
                }
                // Match against the type of `var`.
                match meta.type_knowledge().variable_type() {
                    Some(VariableType::Local { .. }) => {
                        trace!("adding `{var}` to local variables read");
                        locals_read.insert(VariableUse::new(meta, var, access));
                    }
                    Some(VariableType::Component { .. }) => {
                        trace!("adding `{var}` to components read");
                        components_read.insert(VariableUse::new(meta, var, access));
                    }
                    Some(VariableType::Signal { .. }) => {
                        trace!("adding `{var}` to signals read");
                        signals_read.insert(VariableUse::new(meta, var, access));
                    }
                    None => {
                        // If the variable type is unknown we ignore it.
                        trace!("variable `{var}` of unknown type read");
                    }
                }
            }
            Update {
                meta,
                var,
                access,
                rhe,
                ..
            } => {
                // Cache RHS variable use.
                rhe.cache_variable_use();
                locals_read.extend(rhe.locals_read().iter().cloned());
                signals_read.extend(rhe.signals_read().iter().cloned());
                components_read.extend(rhe.components_read().iter().cloned());

                // Cache array index variable use.
                for access in access.iter_mut() {
                    if let AccessType::ArrayAccess(index) = access {
                        index.cache_variable_use();
                        locals_read.extend(index.locals_read().clone());
                        signals_read.extend(index.signals_read().clone());
                        components_read.extend(index.components_read().clone());
                    }
                }
                // Match against the type of `var`.
                match meta.type_knowledge().variable_type() {
                    Some(VariableType::Local { .. }) => {
                        trace!("adding `{var}` to local variables read");
                        locals_read.insert(VariableUse::new(meta, var, &Vec::new()));
                    }
                    Some(VariableType::Component { .. }) => {
                        trace!("adding `{var}` to components read");
                        components_read.insert(VariableUse::new(meta, var, &Vec::new()));
                    }
                    Some(VariableType::Signal { .. }) => {
                        trace!("adding `{var}` to signals read");
                        signals_read.insert(VariableUse::new(meta, var, &Vec::new()));
                    }
                    None => {
                        // If the variable type is unknown we ignore it.
                        trace!("variable `{var}` of unknown type read");
                    }
                }
            }
            Number(_, _) => {}
        }
        self.meta_mut()
            .variable_knowledge_mut()
            .set_locals_read(&locals_read)
            .set_locals_written(&VariableUses::new())
            .set_signals_read(&signals_read)
            .set_signals_written(&VariableUses::new())
            .set_components_read(&components_read)
            .set_components_written(&VariableUses::new());
    }

    fn locals_read(&self) -> &VariableUses {
        self.meta().variable_knowledge().locals_read()
    }

    fn locals_written(&self) -> &VariableUses {
        self.meta().variable_knowledge().locals_written()
    }

    fn signals_read(&self) -> &VariableUses {
        self.meta().variable_knowledge().signals_read()
    }

    fn signals_written(&self) -> &VariableUses {
        self.meta().variable_knowledge().signals_written()
    }

    fn components_read(&self) -> &VariableUses {
        self.meta().variable_knowledge().components_read()
    }

    fn components_written(&self) -> &VariableUses {
        self.meta().variable_knowledge().components_written()
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
                let mut result = lhe.propagate_values(env) || rhe.propagate_values(env);
                match infix_op.propagate_values(lhe.value(), rhe.value()) {
                    Some(value) => {
                        result = result || meta.value_knowledge_mut().set_reduces_to(value)
                    }
                    None => {}
                }
                result
            }
            PrefixOp {
                meta,
                prefix_op,
                rhe,
            } => {
                let mut result = rhe.propagate_values(env);
                match prefix_op.propagate_values(rhe.value()) {
                    Some(value) => {
                        result = result || meta.value_knowledge_mut().set_reduces_to(value)
                    }
                    None => {}
                }
                result
            }
            SwitchOp {
                meta,
                cond,
                if_true,
                if_false,
            } => {
                let mut result = cond.propagate_values(env)
                    | if_true.propagate_values(env)
                    | if_false.propagate_values(env);
                match (cond.value(), if_true.value(), if_false.value()) {
                    (
                        // The case true? value: _
                        Some(Boolean { value: cond }),
                        Some(value),
                        _,
                    ) if *cond => {
                        result = result || meta.value_knowledge_mut().set_reduces_to(value.clone())
                    }
                    (
                        // The case false? _: value
                        Some(Boolean { value: cond }),
                        _,
                        Some(value),
                    ) if !cond => {
                        result = result || meta.value_knowledge_mut().set_reduces_to(value.clone())
                    }
                    (
                        // The case true? value: _
                        Some(FieldElement { value: cond }),
                        Some(value),
                        _,
                    ) if !cond.is_zero() => {
                        result = result || meta.value_knowledge_mut().set_reduces_to(value.clone())
                    }
                    (
                        // The case false? _: value
                        Some(FieldElement { value: cond }),
                        _,
                        Some(value),
                    ) if cond.is_zero() => {
                        result = result || meta.value_knowledge_mut().set_reduces_to(value.clone())
                    }
                    _ => {}
                }
                result
            }
            Variable { meta, name, .. } => match env.get_variable(name) {
                Some(value) => meta.value_knowledge_mut().set_reduces_to(value.clone()),
                None => false,
            },
            Number(meta, value) => {
                let value = FieldElement {
                    value: value.clone(),
                };
                meta.value_knowledge_mut().set_reduces_to(value)
            }
            Call { args, .. } => {
                // TODO: Handle function calls.
                let mut result = false;
                for arg in args {
                    result = result || arg.propagate_values(env);
                }
                result
            }
            Array { values, .. } => {
                // TODO: Handle inline arrays.
                let mut result = false;
                for value in values {
                    result = result || value.propagate_values(env);
                }
                result
            }
            Access { access, .. } => {
                // TODO: Handle array values.
                let mut result = false;
                for access in access.iter_mut() {
                    if let AccessType::ArrayAccess(index) = access {
                        result = result || index.propagate_values(env);
                    }
                }
                result
            }
            Update { access, rhe, .. } => {
                // TODO: Handle array values.
                let mut result = rhe.propagate_values(env);
                for access in access.iter_mut() {
                    if let AccessType::ArrayAccess(index) = access {
                        result = result || index.propagate_values(env);
                    }
                }
                result
            }
            Phi { meta, args, .. } => {
                // Only set the value of the phi expression if all arguments agree on the value.
                let values = args
                    .iter()
                    .map(|name| env.get_variable(name))
                    .collect::<Option<HashSet<_>>>();
                match values {
                    Some(values) if values.len() == 1 => {
                        // This unwrap is safe since the size is non-zero.
                        let value = *values.iter().next().unwrap();
                        meta.value_knowledge_mut().set_reduces_to(value.clone())
                    }
                    _ => false,
                }
            }
        }
    }

    fn is_constant(&self) -> bool {
        self.value().is_some()
    }

    fn is_boolean(&self) -> bool {
        matches!(self.value(), Some(ValueReduction::Boolean { .. }))
    }

    fn is_field_element(&self) -> bool {
        matches!(self.value(), Some(ValueReduction::FieldElement { .. }))
    }

    fn value(&self) -> Option<&ValueReduction> {
        self.meta().value_knowledge().get_reduces_to()
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

impl fmt::Debug for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        use Expression::*;
        match self {
            Number(_, value) => write!(f, "{}", value),
            Variable { name, .. } => {
                write!(f, "{name:?}")
            }
            InfixOp {
                lhe, infix_op, rhe, ..
            } => write!(f, "({lhe:?} {infix_op} {rhe:?})"),
            PrefixOp { prefix_op, rhe, .. } => write!(f, "({prefix_op}{rhe:?})"),
            SwitchOp {
                cond,
                if_true,
                if_false,
                ..
            } => write!(f, "({cond:?}? {if_true:?} : {if_false:?})"),
            Call { name: id, args, .. } => write!(f, "{}({})", id, vec_to_debug(args, ", ")),
            Array { values, .. } => write!(f, "[{}]", vec_to_debug(values, ", ")),
            Access { var, access, .. } => {
                let access = access
                    .iter()
                    .map(|access| match access {
                        AccessType::ArrayAccess(index) => format!("{index:?}"),
                        AccessType::ComponentAccess(name) => name.clone(),
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "access({var:?}, [{access}])")
            }
            Update {
                var, access, rhe, ..
            } => {
                let access = access
                    .iter()
                    .map(|access| match access {
                        AccessType::ArrayAccess(index) => format!("{index:?}"),
                        AccessType::ComponentAccess(name) => name.clone(),
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "update({var:?}, [{access}], {rhe:?})")
            }
            Phi { args, .. } => write!(f, "φ({})", vec_to_debug(args, ", ")),
        }
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        use Expression::*;
        match self {
            Number(_, value) => write!(f, "{}", value),
            Variable { name, .. } => {
                write!(f, "{name}")
            }
            InfixOp {
                lhe, infix_op, rhe, ..
            } => write!(f, "({lhe} {infix_op} {rhe})"),
            PrefixOp { prefix_op, rhe, .. } => write!(f, "{}({})", prefix_op, rhe),
            SwitchOp {
                cond,
                if_true,
                if_false,
                ..
            } => write!(f, "({cond}? {if_true} : {if_false})"),
            Call { name: id, args, .. } => write!(f, "{}({})", id, vec_to_display(args, ", ")),
            Array { values, .. } => write!(f, "[{}]", vec_to_display(values, ", ")),
            Access { var, access, .. } => {
                write!(f, "{var}")?;
                for access in access {
                    write!(f, "{access}")?;
                }
                Ok(())
            }
            Update { rhe, .. } => {
                // `Update` nodes are handled at the statement level. If we are
                // trying to display the RHS of an array assignment, we probably
                // want the `rhe` input.
                write!(f, "{rhe}")
            }
            Phi { args, .. } => write!(f, "φ({})", vec_to_display(args, ", ")),
        }
    }
}

impl fmt::Display for ExpressionInfixOpcode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
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

impl fmt::Display for ExpressionPrefixOpcode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        use ExpressionPrefixOpcode::*;
        match self {
            Sub => f.write_str("-"),
            BoolNot => f.write_str("!"),
            Complement => f.write_str("~"),
        }
    }
}

impl fmt::Display for AccessType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        use AccessType::*;
        match self {
            ArrayAccess(index) => write!(f, "[{index}]"),
            ComponentAccess(name) => write!(f, ".{name}"),
        }
    }
}

#[must_use]
fn vec_to_debug<T: fmt::Debug>(elems: &[T], sep: &str) -> String {
    elems
        .iter()
        .map(|elem| format!("{elem:?}"))
        .collect::<Vec<String>>()
        .join(sep)
}

#[must_use]
fn vec_to_display<T: fmt::Display>(elems: &[T], sep: &str) -> String {
    elems
        .iter()
        .map(|elem| format!("{elem}"))
        .collect::<Vec<String>>()
        .join(sep)
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
            name: VariableName::from_name("v"),
        };
        let mut env = ValueEnvironment::new();
        env.add_variable(
            &VariableName::from_name("v"),
            &FieldElement { value: 3u64.into() },
        );
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
            expr.value(),
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
            expr.value(),
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
        assert_eq!(expr.value(), Some(&FieldElement { value: 2u64.into() }));
    }
}
