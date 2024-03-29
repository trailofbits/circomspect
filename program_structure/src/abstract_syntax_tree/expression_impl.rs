use std::fmt::{Debug, Display, Error, Formatter};

use super::ast::*;
use super::expression_builders::build_anonymous_component;

impl Expression {
    pub fn meta(&self) -> &Meta {
        use Expression::*;
        match self {
            InfixOp { meta, .. }
            | PrefixOp { meta, .. }
            | InlineSwitchOp { meta, .. }
            | Variable { meta, .. }
            | ParallelOp { meta, .. }
            | Number(meta, ..)
            | Call { meta, .. }
            | AnonymousComponent { meta, .. }
            | ArrayInLine { meta, .. }
            | Tuple { meta, .. } => meta,
        }
    }
    pub fn meta_mut(&mut self) -> &mut Meta {
        use Expression::*;
        match self {
            InfixOp { meta, .. }
            | PrefixOp { meta, .. }
            | InlineSwitchOp { meta, .. }
            | Variable { meta, .. }
            | ParallelOp { meta, .. }
            | Number(meta, ..)
            | Call { meta, .. }
            | AnonymousComponent { meta, .. }
            | ArrayInLine { meta, .. }
            | Tuple { meta, .. } => meta,
        }
    }

    pub fn is_array(&self) -> bool {
        use Expression::*;
        matches!(self, ArrayInLine { .. })
    }

    pub fn is_infix(&self) -> bool {
        use Expression::*;
        matches!(self, InfixOp { .. })
    }

    pub fn is_prefix(&self) -> bool {
        use Expression::*;
        matches!(self, PrefixOp { .. })
    }

    pub fn is_switch(&self) -> bool {
        use Expression::*;
        matches!(self, InlineSwitchOp { .. })
    }

    pub fn is_variable(&self) -> bool {
        use Expression::*;
        matches!(self, Variable { .. })
    }

    pub fn is_number(&self) -> bool {
        use Expression::*;
        matches!(self, Number(..))
    }

    pub fn is_call(&self) -> bool {
        use Expression::*;
        matches!(self, Call { .. })
    }

    pub fn is_parallel(&self) -> bool {
        use Expression::*;
        matches!(self, ParallelOp { .. })
    }

    pub fn is_tuple(&self) -> bool {
        use Expression::*;
        matches!(self, Tuple { .. })
    }

    pub fn is_anonymous_component(&self) -> bool {
        use Expression::*;
        matches!(self, AnonymousComponent { .. })
    }

    pub fn make_anonymous_parallel(self) -> Expression {
        use Expression::*;
        match self {
            AnonymousComponent { meta, id, params, signals, names, .. } => {
                build_anonymous_component(meta, id, params, signals, names, true)
            }
            _ => self,
        }
    }
}

impl FillMeta for Expression {
    fn fill(&mut self, file_id: usize, element_id: &mut usize) {
        use Expression::*;
        self.meta_mut().elem_id = *element_id;
        *element_id += 1;
        match self {
            Tuple { meta, values } => fill_tuple(meta, values, file_id, element_id),
            Number(meta, _) => fill_number(meta, file_id, element_id),
            Variable { meta, access, .. } => fill_variable(meta, access, file_id, element_id),
            InfixOp { meta, lhe, rhe, .. } => fill_infix(meta, lhe, rhe, file_id, element_id),
            PrefixOp { meta, rhe, .. } => fill_prefix(meta, rhe, file_id, element_id),
            ParallelOp { meta, rhe, .. } => fill_parallel(meta, rhe, file_id, element_id),
            InlineSwitchOp { meta, cond, if_false, if_true, .. } => {
                fill_inline_switch_op(meta, cond, if_true, if_false, file_id, element_id)
            }
            Call { meta, args, .. } => fill_call(meta, args, file_id, element_id),
            ArrayInLine { meta, values, .. } => {
                fill_array_inline(meta, values, file_id, element_id)
            }
            AnonymousComponent { meta, params, signals, .. } => {
                fill_anonymous_component(meta, params, signals, file_id, element_id)
            }
        }
    }
}

fn fill_number(meta: &mut Meta, file_id: usize, _element_id: &mut usize) {
    meta.set_file_id(file_id);
}

fn fill_variable(meta: &mut Meta, access: &mut [Access], file_id: usize, element_id: &mut usize) {
    meta.set_file_id(file_id);
    for acc in access {
        if let Access::ArrayAccess(e) = acc {
            e.fill(file_id, element_id)
        }
    }
}

fn fill_infix(
    meta: &mut Meta,
    lhe: &mut Expression,
    rhe: &mut Expression,
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    lhe.fill(file_id, element_id);
    rhe.fill(file_id, element_id);
}

fn fill_prefix(meta: &mut Meta, rhe: &mut Expression, file_id: usize, element_id: &mut usize) {
    meta.set_file_id(file_id);
    rhe.fill(file_id, element_id);
}

fn fill_inline_switch_op(
    meta: &mut Meta,
    cond: &mut Expression,
    if_true: &mut Expression,
    if_false: &mut Expression,
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    cond.fill(file_id, element_id);
    if_true.fill(file_id, element_id);
    if_false.fill(file_id, element_id);
}

fn fill_call(meta: &mut Meta, args: &mut [Expression], file_id: usize, element_id: &mut usize) {
    meta.set_file_id(file_id);
    for a in args {
        a.fill(file_id, element_id);
    }
}

fn fill_array_inline(
    meta: &mut Meta,
    values: &mut [Expression],
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    for v in values {
        v.fill(file_id, element_id);
    }
}

fn fill_anonymous_component(
    meta: &mut Meta,
    params: &mut [Expression],
    signals: &mut [Expression],
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    for param in params {
        param.fill(file_id, element_id);
    }
    for signal in signals {
        signal.fill(file_id, element_id);
    }
}

fn fill_tuple(meta: &mut Meta, values: &mut [Expression], file_id: usize, element_id: &mut usize) {
    meta.set_file_id(file_id);
    for value in values {
        value.fill(file_id, element_id);
    }
}

fn fill_parallel(meta: &mut Meta, rhe: &mut Expression, file_id: usize, element_id: &mut usize) {
    meta.set_file_id(file_id);
    rhe.fill(file_id, element_id);
}

impl Debug for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        use Expression::*;
        match self {
            InfixOp { .. } => write!(f, "Expression::InfixOp"),
            PrefixOp { .. } => write!(f, "Expression::PrefixOp"),
            InlineSwitchOp { .. } => write!(f, "Expression::InlineSwitchOp"),
            Variable { .. } => write!(f, "Expression::Variable"),
            ParallelOp { .. } => write!(f, "Expression::ParallelOp"),
            Number(..) => write!(f, "Expression::Number"),
            Call { .. } => write!(f, "Expression::Call"),
            AnonymousComponent { .. } => write!(f, "Expression::AnonymousComponent"),
            ArrayInLine { .. } => write!(f, "Expression::ArrayInline"),
            Tuple { .. } => write!(f, "Expression::Tuple"),
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        use Expression::*;
        match self {
            Tuple { values, .. } => write!(f, "({})", vec_to_string(values)),
            Number(_, value) => write!(f, "{value}"),
            Variable { name, access, .. } => {
                write!(f, "{name}")?;
                for access in access {
                    write!(f, "{access}")?;
                }
                Ok(())
            }
            ParallelOp { rhe, .. } => write!(f, "parallel {rhe}"),
            InfixOp { lhe, infix_op, rhe, .. } => write!(f, "({lhe} {infix_op} {rhe})"),
            PrefixOp { prefix_op, rhe, .. } => write!(f, "{prefix_op}({rhe})"),
            InlineSwitchOp { cond, if_true, if_false, .. } => {
                write!(f, "({cond}? {if_true} : {if_false})")
            }
            Call { id, args, .. } => write!(f, "{id}({})", vec_to_string(args)),
            ArrayInLine { values, .. } => write!(f, "[{}]", vec_to_string(values)),
            AnonymousComponent { id, params, signals, names, .. } => {
                write!(f, "{id}({})({})", vec_to_string(params), signals_to_string(names, signals))
            }
        }
    }
}

impl Display for ExpressionInfixOpcode {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
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
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        use ExpressionPrefixOpcode::*;
        match self {
            Sub => f.write_str("-"),
            BoolNot => f.write_str("!"),
            Complement => f.write_str("~"),
        }
    }
}

impl Display for Access {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        use Access::*;
        match self {
            ArrayAccess(index) => write!(f, "[{index}]"),
            ComponentAccess(name) => write!(f, ".{name}"),
        }
    }
}

fn vec_to_string(elems: &[Expression]) -> String {
    elems.iter().map(|arg| arg.to_string()).collect::<Vec<String>>().join(", ")
}

fn signals_to_string(names: &Option<Vec<(AssignOp, String)>>, signals: &[Expression]) -> String {
    if let Some(names) = names {
        names
            .iter()
            .zip(signals.iter())
            .map(|((op, name), signal)| format!("{name} {op} {signal}"))
            .collect::<Vec<_>>()
    } else {
        signals.iter().map(|signal| signal.to_string()).collect::<Vec<_>>()
    }
    .join(", ")
}
