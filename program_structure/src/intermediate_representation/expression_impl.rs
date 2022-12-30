use log::trace;
use num_traits::Zero;
use std::fmt;
use std::hash::{Hash, Hasher};

use circom_algebra::modular_arithmetic;

use super::declarations::Declarations;
use super::degree_meta::{Degree, DegreeEnvironment, DegreeMeta, DegreeRange};
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
            | InlineArray { meta, .. }
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
            | InlineArray { meta, .. }
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
                InfixOp { lhe: self_lhe, infix_op: self_op, rhe: self_rhe, .. },
                InfixOp { lhe: other_lhe, infix_op: other_op, rhe: other_rhe, .. },
            ) => self_op == other_op && self_lhe == other_lhe && self_rhe == other_rhe,
            (
                PrefixOp { prefix_op: self_op, rhe: self_rhe, .. },
                PrefixOp { prefix_op: other_op, rhe: other_rhe, .. },
            ) => self_op == other_op && self_rhe == other_rhe,
            (
                SwitchOp { cond: self_cond, if_true: self_true, if_false: self_false, .. },
                SwitchOp { cond: other_cond, if_true: other_true, if_false: other_false, .. },
            ) => self_cond == other_cond && self_true == other_true && self_false == other_false,
            (Variable { name: self_name, .. }, Variable { name: other_name, .. }) => {
                self_name == other_name
            }
            (Number(_, self_value), Number(_, other_value)) => self_value == other_value,
            (
                Call { name: self_id, args: self_args, .. },
                Call { name: other_id, args: other_args, .. },
            ) => self_id == other_id && self_args == other_args,
            (InlineArray { values: self_values, .. }, InlineArray { values: other_values, .. }) => {
                self_values == other_values
            }
            (
                Update { var: self_var, access: self_access, rhe: self_rhe, .. },
                Update { var: other_var, access: other_access, rhe: other_rhe, .. },
            ) => self_var == other_var && self_access == other_access && self_rhe == other_rhe,
            (
                Access { var: self_var, access: self_access, .. },
                Access { var: other_var, access: other_access, .. },
            ) => self_var == other_var && self_access == other_access,
            (Phi { args: self_args, .. }, Phi { args: other_args, .. }) => self_args == other_args,
            _ => false,
        }
    }
}

impl Eq for Expression {}

impl Hash for Expression {
    fn hash<H: Hasher>(&self, state: &mut H) {
        use Expression::*;
        match self {
            InfixOp { lhe, rhe, .. } => {
                lhe.hash(state);
                rhe.hash(state);
            }
            PrefixOp { rhe, .. } => {
                rhe.hash(state);
            }
            SwitchOp { cond, if_true, if_false, .. } => {
                cond.hash(state);
                if_true.hash(state);
                if_false.hash(state);
            }
            Variable { name, .. } => {
                name.hash(state);
            }
            Call { args, .. } => {
                args.hash(state);
            }
            InlineArray { values, .. } => {
                values.hash(state);
            }
            Access { var, access, .. } => {
                var.hash(state);
                access.hash(state);
            }
            Update { var, access, rhe, .. } => {
                var.hash(state);
                access.hash(state);
                rhe.hash(state);
            }
            Phi { args, .. } => {
                args.hash(state);
            }
            Number(_, value) => {
                value.hash(state);
            }
        }
    }
}

impl DegreeMeta for Expression {
    fn propagate_degrees(&mut self, env: &DegreeEnvironment) -> bool {
        let mut result = false;

        use Degree::*;
        use Expression::*;
        match self {
            InfixOp { meta, lhe, rhe, infix_op } => {
                result = result || lhe.propagate_degrees(env);
                result = result || rhe.propagate_degrees(env);
                let range = infix_op.propagate_degrees(lhe.degree(), rhe.degree());
                if let Some(range) = range {
                    result = result || meta.degree_knowledge_mut().set_degree(&range);
                }
                result
            }
            PrefixOp { meta, rhe, prefix_op, .. } => {
                result = result || rhe.propagate_degrees(env);
                let range = prefix_op.propagate_degrees(rhe.degree());
                if let Some(range) = range {
                    result = result || meta.degree_knowledge_mut().set_degree(&range);
                }
                result
            }
            SwitchOp { meta, cond, if_true, if_false, .. } => {
                // If the condition has constant degree, the expression can be
                // desugared using an if-statement and the maximum degree in
                // each case will be the maximum of the individual if- and
                // else-case degrees.
                result = result || cond.propagate_degrees(env);
                result = result || if_true.propagate_degrees(env);
                result = result || if_false.propagate_degrees(env);
                let Some(range) = cond.degree() else {
                    return result;
                };
                if range.is_constant() {
                    // The condition has constant degree.
                    if let Some(range) =
                        DegreeRange::iter_opt([if_true.degree(), if_false.degree()])
                    {
                        result = result || meta.degree_knowledge_mut().set_degree(&range);
                    }
                }
                result
            }
            Variable { meta, name } => {
                if let Some(range) = env.degree(name) {
                    result = result || meta.degree_knowledge_mut().set_degree(range);
                }
                result
            }
            Call { meta, args, .. } => {
                for arg in args.iter_mut() {
                    result = result || arg.propagate_degrees(env);
                }
                // If one or more non-constant arguments is passed to the function we cannot
                // say anything about the degree of the output. If the function only takes
                // constant arguments the output must also be constant.
                if args.iter().all(|arg| {
                    if let Some(range) = arg.degree() {
                        range.is_constant()
                    } else {
                        false
                    }
                }) {
                    result = result || meta.degree_knowledge_mut().set_degree(&Constant.into())
                }
                result
            }
            InlineArray { meta, values } => {
                // The degree range of an array is the infimum of the ranges of all elements.
                for value in values.iter_mut() {
                    result = result || value.propagate_degrees(env);
                }
                let range = DegreeRange::iter_opt(values.iter().map(|value| value.degree()));
                if let Some(range) = range {
                    result = result || meta.degree_knowledge_mut().set_degree(&range);
                }
                result
            }
            Access { meta, var, access } => {
                // Accesses are ignored when determining the degree of a variable.
                for access in access.iter_mut() {
                    if let AccessType::ArrayAccess(index) = access {
                        result = result || index.propagate_degrees(env);
                    }
                }
                if let Some(range) = env.degree(var) {
                    result = result || meta.degree_knowledge_mut().set_degree(range);
                }
                result
            }
            Update { meta, var, access, rhe, .. } => {
                // Accesses are ignored when determining the degree of a variable.
                result = result || rhe.propagate_degrees(env);
                for access in access.iter_mut() {
                    if let AccessType::ArrayAccess(index) = access {
                        result = result || index.propagate_degrees(env);
                    }
                }
                if env.degree(var).is_none() {
                    // This is the first assignment to the array. The degree is given by the RHS.
                    if let Some(range) = rhe.degree() {
                        result = result || meta.degree_knowledge_mut().set_degree(range);
                    }
                } else {
                    // The array has been assigned to previously. The degree is the infimum of
                    // the degrees of `var` and the RHS.
                    let range = DegreeRange::iter_opt([env.degree(var), rhe.degree()]);
                    if let Some(range) = range {
                        result = result || meta.degree_knowledge_mut().set_degree(&range);
                    }
                }
                result
            }
            Phi { meta, args } => {
                // The degree range of a phi expression is the infimum of the ranges of all the arguments.
                let range = DegreeRange::iter_opt(args.iter().map(|arg| env.degree(arg)));
                if let Some(range) = range {
                    result = result || meta.degree_knowledge_mut().set_degree(&range);
                }
                result
            }
            Number(meta, _) => {
                // Constants have constant degree.
                meta.degree_knowledge_mut().set_degree(&Constant.into())
            }
        }
    }

    fn degree(&self) -> Option<&DegreeRange> {
        self.meta().degree_knowledge().degree()
    }
}

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
            SwitchOp { cond, if_true, if_false, .. } => {
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
            InlineArray { values, .. } => {
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
            Update { meta, var, access, rhe, .. } => {
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
            SwitchOp { cond, if_true, if_false, .. } => {
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
                    Some(VariableType::Local) => {
                        trace!("adding `{name:?}` to local variables read");
                        locals_read.insert(VariableUse::new(meta, name, &Vec::new()));
                    }
                    Some(VariableType::Component | VariableType::AnonymousComponent) => {
                        trace!("adding `{name:?}` to components read");
                        components_read.insert(VariableUse::new(meta, name, &Vec::new()));
                    }
                    Some(VariableType::Signal(_, _)) => {
                        trace!("adding `{name:?}` to signals read");
                        signals_read.insert(VariableUse::new(meta, name, &Vec::new()));
                    }
                    None => {
                        // If the variable type is unknown we ignore it.
                        trace!("variable `{name:?}` of unknown type read");
                    }
                }
            }
            Call { args, .. } => {
                for arg in args {
                    arg.cache_variable_use();
                    locals_read.extend(arg.locals_read().clone());
                    signals_read.extend(arg.signals_read().clone());
                    components_read.extend(arg.components_read().clone());
                }
            }
            Phi { meta, args } => {
                locals_read
                    .extend(args.iter().map(|name| VariableUse::new(meta, name, &Vec::new())));
            }
            InlineArray { values, .. } => {
                for value in values {
                    value.cache_variable_use();
                    locals_read.extend(value.locals_read().clone());
                    signals_read.extend(value.signals_read().clone());
                    components_read.extend(value.components_read().clone());
                }
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
                    Some(VariableType::Local) => {
                        trace!("adding `{var:?}` to local variables read");
                        locals_read.insert(VariableUse::new(meta, var, access));
                    }
                    Some(VariableType::Component | VariableType::AnonymousComponent) => {
                        trace!("adding `{var:?}` to components read");
                        components_read.insert(VariableUse::new(meta, var, access));
                    }
                    Some(VariableType::Signal(_, _)) => {
                        trace!("adding `{var:?}` to signals read");
                        signals_read.insert(VariableUse::new(meta, var, access));
                    }
                    None => {
                        // If the variable type is unknown we ignore it.
                        trace!("variable `{var:?}` of unknown type read");
                    }
                }
            }
            Update { meta, var, access, rhe, .. } => {
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
                    Some(VariableType::Local) => {
                        trace!("adding `{var:?}` to local variables read");
                        locals_read.insert(VariableUse::new(meta, var, &Vec::new()));
                    }
                    Some(VariableType::Component | VariableType::AnonymousComponent) => {
                        trace!("adding `{var:?}` to components read");
                        components_read.insert(VariableUse::new(meta, var, &Vec::new()));
                    }
                    Some(VariableType::Signal(_, _)) => {
                        trace!("adding `{var:?}` to signals read");
                        signals_read.insert(VariableUse::new(meta, var, &Vec::new()));
                    }
                    None => {
                        // If the variable type is unknown we ignore it.
                        trace!("variable `{var:?}` of unknown type read");
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
            InfixOp { meta, lhe, infix_op, rhe, .. } => {
                let result = lhe.propagate_values(env) || rhe.propagate_values(env);
                let value = infix_op.propagate_values(&lhe.value(), &rhe.value(), env);
                result || meta.value_knowledge_mut().set_reduces_to(value)
            }
            PrefixOp { meta, prefix_op, rhe } => {
                let result = rhe.propagate_values(env);
                let value = prefix_op.propagate_values(&rhe.value(), env);
                result || meta.value_knowledge_mut().set_reduces_to(value)
            }
            SwitchOp { meta, cond, if_true, if_false } => {
                let result = cond.propagate_values(env)
                    | if_true.propagate_values(env)
                    | if_false.propagate_values(env);
                result
                    || match (cond.value(), if_true.value(), if_false.value()) {
                        (Boolean(cond), t, f) => {
                            let value = match cond {
                                Some(true) => t.clone(),
                                Some(false) => f.clone(),
                                None => t.union(&f),
                            };
                            meta.value_knowledge_mut().set_reduces_to(value.clone())
                        }

                        (FieldElement(cond), t, f) => {
                            let value = match cond.map(|c| !c.is_zero()) {
                                Some(true) => t.clone(),
                                Some(false) => f.clone(),
                                None => t.union(&f),
                            };

                            meta.value_knowledge_mut().set_reduces_to(value.clone())
                        }

                        (Unknown, t, f) => meta.value_knowledge_mut().set_reduces_to(t.union(&f)),

                        (Impossible, _, _) => meta.value_knowledge_mut().set_reduces_to(Impossible),
                    }
            }
            Variable { meta, name, .. } => {
                meta.value_knowledge_mut().set_reduces_to(env.get_variable(name))
            }
            Number(meta, value) => {
                let value = FieldElement(Some(value.clone()));
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
            InlineArray { values, .. } => {
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
                // set the value of the phi expression to the union of all
                // possible inputs
                let mut value = ValueReduction::default();
                for name in args.iter() {
                    let v = env.get_variable(name);
                    value = value.union(&v);
                }
                meta.value_knowledge_mut().set_reduces_to(value)
            }
        }
    }

    fn is_constant(&self) -> bool {
        self.value().is_constant()
    }

    fn is_boolean(&self) -> bool {
        matches!(self.value(), ValueReduction::Boolean(Some(_)))
    }

    fn is_field_element(&self) -> bool {
        matches!(self.value(), ValueReduction::FieldElement(Some(_)))
    }

    fn value(&self) -> ValueReduction {
        self.meta().value_knowledge().clone()
    }
}

impl ExpressionInfixOpcode {
    fn propagate_degrees(
        &self,
        lhr: Option<&DegreeRange>,
        rhr: Option<&DegreeRange>,
    ) -> Option<DegreeRange> {
        if let (Some(lhr), Some(rhr)) = (lhr, rhr) {
            use ExpressionInfixOpcode::*;
            match self {
                Add => Some(lhr.add(rhr)),
                Sub => Some(lhr.infix_sub(rhr)),
                Mul => Some(lhr.mul(rhr)),
                Pow => Some(lhr.pow(rhr)),
                Div => Some(lhr.div(rhr)),
                IntDiv => Some(lhr.int_div(rhr)),
                Mod => Some(lhr.modulo(rhr)),
                ShiftL => Some(lhr.shift_left(rhr)),
                ShiftR => Some(lhr.shift_right(rhr)),
                Lesser => Some(lhr.lesser(rhr)),
                Greater => Some(lhr.greater(rhr)),
                LesserEq => Some(lhr.lesser_eq(rhr)),
                GreaterEq => Some(lhr.greater_eq(rhr)),
                Eq => Some(lhr.equal(rhr)),
                NotEq => Some(lhr.not_equal(rhr)),
                BitOr => Some(lhr.bit_or(rhr)),
                BitXor => Some(lhr.bit_xor(rhr)),
                BitAnd => Some(lhr.bit_and(rhr)),
                BoolOr => Some(lhr.bool_or(rhr)),
                BoolAnd => Some(lhr.bool_and(rhr)),
            }
        } else {
            None
        }
    }

    fn propagate_values(
        &self,
        lhv: &ValueReduction,
        rhv: &ValueReduction,
        env: &ValueEnvironment,
    ) -> ValueReduction {
        let p = env.prime();

        use ValueReduction::*;

        match (lhv, rhv) {
            // lhv and rhv reduce to two field elements.
            (FieldElement(Some(lhv)), FieldElement(Some(rhv))) => {
                use ExpressionInfixOpcode::*;
                match self {
                    Mul => {
                        let value = modular_arithmetic::mul(lhv, rhv, p);
                        FieldElement(Some(value))
                    }
                    Div => modular_arithmetic::div(lhv, rhv, p)
                        .ok()
                        .map(|value| FieldElement(Some(value)))
                        .unwrap_or(Impossible),
                    Add => {
                        let value = modular_arithmetic::add(lhv, rhv, p);
                        FieldElement(Some(value))
                    }
                    Sub => {
                        let value = modular_arithmetic::sub(lhv, rhv, p);
                        FieldElement(Some(value))
                    }
                    Pow => {
                        let value = modular_arithmetic::pow(lhv, rhv, p);
                        FieldElement(Some(value))
                    }
                    IntDiv => modular_arithmetic::idiv(lhv, rhv, p)
                        .ok()
                        .map(|value| FieldElement(Some(value)))
                        .unwrap_or(Impossible),
                    Mod => modular_arithmetic::mod_op(lhv, rhv, p)
                        .ok()
                        .map(|value| FieldElement(Some(value)))
                        .unwrap_or(Impossible),
                    ShiftL => modular_arithmetic::shift_l(lhv, rhv, p)
                        .ok()
                        .map(|value| FieldElement(Some(value)))
                        .unwrap_or(Impossible),
                    ShiftR => modular_arithmetic::shift_r(lhv, rhv, p)
                        .ok()
                        .map(|value| FieldElement(Some(value)))
                        .unwrap_or(Impossible),
                    LesserEq => {
                        let value = modular_arithmetic::lesser_eq(lhv, rhv, p);
                        Boolean(Some(modular_arithmetic::as_bool(&value, p)))
                    }
                    GreaterEq => {
                        let value = modular_arithmetic::greater_eq(lhv, rhv, p);
                        Boolean(Some(modular_arithmetic::as_bool(&value, p)))
                    }
                    Lesser => {
                        let value = modular_arithmetic::lesser(lhv, rhv, p);
                        Boolean(Some(modular_arithmetic::as_bool(&value, p)))
                    }
                    Greater => {
                        let value = modular_arithmetic::greater(lhv, rhv, p);
                        Boolean(Some(modular_arithmetic::as_bool(&value, p)))
                    }
                    Eq => {
                        let value = modular_arithmetic::eq(lhv, rhv, p);
                        Boolean(Some(modular_arithmetic::as_bool(&value, p)))
                    }
                    NotEq => {
                        let value = modular_arithmetic::not_eq(lhv, rhv, p);
                        Boolean(Some(modular_arithmetic::as_bool(&value, p)))
                    }
                    BitOr => {
                        let value = modular_arithmetic::bit_or(lhv, rhv, p);
                        FieldElement(Some(value))
                    }
                    BitAnd => {
                        let value = modular_arithmetic::bit_and(lhv, rhv, p);
                        FieldElement(Some(value))
                    }
                    BitXor => {
                        let value = modular_arithmetic::bit_xor(lhv, rhv, p);
                        FieldElement(Some(value))
                    }
                    // Remaining operations do not make sense.
                    // TODO: Add report/error propagation here.
                    _ => Unknown,
                }
            }
            // lhv and rhv reduce to two booleans.
            (Boolean(lhv), Boolean(rhv)) => {
                use ExpressionInfixOpcode::*;
                match self {
                    BoolAnd => Boolean(match (lhv, rhv) {
                        (Some(true), r) => r.clone(),
                        (Some(false), _) => Some(false),
                        (None, Some(false)) => Some(false),
                        _ => None,
                    }),
                    BoolOr => Boolean(match (lhv, rhv) {
                        (Some(false), r) => r.clone(),
                        (Some(true), _) => Some(true),
                        (None, Some(true)) => Some(true),
                        _ => None,
                    }),
                    // Remaining operations do not make sense.
                    // TODO: Add report propagation here as well.
                    _ => Unknown,
                }
            }
            _ => {
                use ExpressionInfixOpcode::*;
                // TODO: should we check the input types?
                match self {
                    Mul | Div | Add | Sub | Pow | IntDiv | Mod | ShiftL | ShiftR | BitOr
                    | BitAnd | BitXor => FieldElement(None),

                    LesserEq | GreaterEq | Lesser | Greater | Eq | NotEq | BoolAnd | BoolOr => {
                        Boolean(None)
                    }
                }
            }
        }
    }
}

impl ExpressionPrefixOpcode {
    fn propagate_degrees(&self, range: Option<&DegreeRange>) -> Option<DegreeRange> {
        if let Some(range) = range {
            use ExpressionPrefixOpcode::*;
            match self {
                Sub => Some(range.prefix_sub()),
                Complement => Some(range.complement()),
                BoolNot => Some(range.bool_not()),
            }
        } else {
            None
        }
    }

    fn propagate_values(&self, rhe: &ValueReduction, env: &ValueEnvironment) -> ValueReduction {
        let p = env.prime();

        use ValueReduction::*;
        match rhe {
            // arg reduces to a field element.
            FieldElement(arg) => {
                use ExpressionPrefixOpcode::*;
                match self {
                    Sub => {
                        FieldElement(arg.as_ref().map(|arg| modular_arithmetic::prefix_sub(arg, p)))
                    }
                    Complement => FieldElement(
                        arg.as_ref().map(|arg| modular_arithmetic::complement_256(arg, p)),
                    ),
                    // Remaining operations do not make sense.
                    // TODO: Add report propagation here as well.
                    _ => Unknown,
                }
            }
            // arg reduces to a boolean.
            Boolean(arg) => {
                use ExpressionPrefixOpcode::*;
                match self {
                    BoolNot => Boolean(arg.map(|x| !x)),
                    // Remaining operations do not make sense.
                    // TODO: Add report propagation here as well.
                    _ => Unknown,
                }
            }
            _ => Unknown,
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
            InfixOp { lhe, infix_op, rhe, .. } => write!(f, "({lhe:?} {infix_op} {rhe:?})"),
            PrefixOp { prefix_op, rhe, .. } => write!(f, "({prefix_op}{rhe:?})"),
            SwitchOp { cond, if_true, if_false, .. } => {
                write!(f, "({cond:?}? {if_true:?} : {if_false:?})")
            }
            Call { name: id, args, .. } => write!(f, "{}({})", id, vec_to_debug(args, ", ")),
            InlineArray { values, .. } => write!(f, "[{}]", vec_to_debug(values, ", ")),
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
            Update { var, access, rhe, .. } => {
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
            InfixOp { lhe, infix_op, rhe, .. } => write!(f, "({lhe} {infix_op} {rhe})"),
            PrefixOp { prefix_op, rhe, .. } => write!(f, "{}({})", prefix_op, rhe),
            SwitchOp { cond, if_true, if_false, .. } => {
                write!(f, "({cond}? {if_true} : {if_false})")
            }
            Call { name: id, args, .. } => write!(f, "{}({})", id, vec_to_display(args, ", ")),
            InlineArray { values, .. } => write!(f, "[{}]", vec_to_display(values, ", ")),
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

impl fmt::Debug for AccessType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        use AccessType::*;
        match self {
            ArrayAccess(index) => write!(f, "{index:?}"),
            ComponentAccess(name) => write!(f, "{name:?}"),
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
    elems.iter().map(|elem| format!("{elem:?}")).collect::<Vec<String>>().join(sep)
}

#[must_use]
fn vec_to_display<T: fmt::Display>(elems: &[T], sep: &str) -> String {
    elems.iter().map(|elem| format!("{elem}")).collect::<Vec<String>>().join(sep)
}

#[cfg(test)]
mod tests {
    use crate::constants::{UsefulConstants, Curve};

    use super::*;

    #[test]
    fn test_propagate_values() {
        use Expression::*;
        use ExpressionInfixOpcode::*;
        use ValueReduction::*;
        let mut lhe = Number(Meta::default(), 7u64.into());
        let mut rhe = Variable { meta: Meta::default(), name: VariableName::from_string("v") };
        let constants = UsefulConstants::new(&Curve::default());
        let mut env = ValueEnvironment::new(&constants);
        env.add_variable(&VariableName::from_string("v"), &FieldElement(Some(3u64.into())));
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
        assert_eq!(expr.value(), FieldElement(Some(21u64.into())));

        // Infix addition.
        let mut expr = InfixOp {
            meta: Meta::default(),
            infix_op: Add,
            lhe: Box::new(lhe.clone()),
            rhe: Box::new(rhe.clone()),
        };
        expr.propagate_values(&mut env.clone());
        assert_eq!(expr.value(), FieldElement(Some(10u64.into())));

        // Infix integer division.
        let mut expr = InfixOp {
            meta: Meta::default(),
            infix_op: IntDiv,
            lhe: Box::new(lhe.clone()),
            rhe: Box::new(rhe.clone()),
        };
        expr.propagate_values(&mut env.clone());
        assert_eq!(expr.value(), FieldElement(Some(2u64.into())));
    }
}
