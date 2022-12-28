use std::fmt::{Debug, Display, Error, Formatter};

use super::ast::*;

impl Statement {
    pub fn get_meta(&self) -> &Meta {
        use Statement::*;
        match self {
            IfThenElse { meta, .. }
            | While { meta, .. }
            | Return { meta, .. }
            | Declaration { meta, .. }
            | Substitution { meta, .. }
            | MultiSubstitution { meta, .. }
            | LogCall { meta, .. }
            | Block { meta, .. }
            | Assert { meta, .. }
            | ConstraintEquality { meta, .. }
            | InitializationBlock { meta, .. } => meta,
        }
    }
    pub fn get_mut_meta(&mut self) -> &mut Meta {
        use Statement::*;
        match self {
            IfThenElse { meta, .. }
            | While { meta, .. }
            | Return { meta, .. }
            | Declaration { meta, .. }
            | Substitution { meta, .. }
            | MultiSubstitution { meta, .. }
            | LogCall { meta, .. }
            | Block { meta, .. }
            | Assert { meta, .. }
            | ConstraintEquality { meta, .. }
            | InitializationBlock { meta, .. } => meta,
        }
    }

    pub fn is_if_then_else(&self) -> bool {
        use Statement::*;
        matches!(self, IfThenElse { .. })
    }

    pub fn is_while(&self) -> bool {
        use Statement::*;
        matches!(self, While { .. })
    }

    pub fn is_return(&self) -> bool {
        use Statement::*;
        matches!(self, Return { .. })
    }

    pub fn is_initialization_block(&self) -> bool {
        use Statement::*;
        matches!(self, InitializationBlock { .. })
    }

    pub fn is_declaration(&self) -> bool {
        use Statement::*;
        matches!(self, Declaration { .. })
    }

    pub fn is_substitution(&self) -> bool {
        use Statement::*;
        matches!(self, Substitution { .. })
    }

    pub fn is_multi_substitution(&self) -> bool {
        use Statement::*;
        matches!(self, MultiSubstitution { .. })
    }

    pub fn is_constraint_equality(&self) -> bool {
        use Statement::*;
        matches!(self, ConstraintEquality { .. })
    }

    pub fn is_log_call(&self) -> bool {
        use Statement::*;
        matches!(self, LogCall { .. })
    }

    pub fn is_block(&self) -> bool {
        use Statement::*;
        matches!(self, Block { .. })
    }

    pub fn is_assert(&self) -> bool {
        use Statement::*;
        matches!(self, Assert { .. })
    }
}

impl FillMeta for Statement {
    fn fill(&mut self, file_id: usize, element_id: &mut usize) {
        use Statement::*;
        self.get_mut_meta().elem_id = *element_id;
        *element_id += 1;
        match self {
            IfThenElse { meta, cond, if_case, else_case, .. } => {
                fill_conditional(meta, cond, if_case, else_case, file_id, element_id)
            }
            While { meta, cond, stmt } => fill_while(meta, cond, stmt, file_id, element_id),
            Return { meta, value } => fill_return(meta, value, file_id, element_id),
            InitializationBlock { meta, initializations, .. } => {
                fill_initialization(meta, initializations, file_id, element_id)
            }
            Declaration { meta, dimensions, .. } => {
                fill_declaration(meta, dimensions, file_id, element_id)
            }
            Substitution { meta, access, rhe, .. } => {
                fill_substitution(meta, access, rhe, file_id, element_id)
            }
            MultiSubstitution { meta, lhe, rhe, .. } => {
                fill_multi_substitution(meta, lhe, rhe, file_id, element_id);
            }
            ConstraintEquality { meta, lhe, rhe } => {
                fill_constraint_equality(meta, lhe, rhe, file_id, element_id)
            }
            LogCall { meta, args, .. } => fill_log_call(meta, args, file_id, element_id),
            Block { meta, stmts, .. } => fill_block(meta, stmts, file_id, element_id),
            Assert { meta, arg, .. } => fill_assert(meta, arg, file_id, element_id),
        }
    }
}

fn fill_conditional(
    meta: &mut Meta,
    cond: &mut Expression,
    if_case: &mut Statement,
    else_case: &mut Option<Box<Statement>>,
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    cond.fill(file_id, element_id);
    if_case.fill(file_id, element_id);
    if let Option::Some(s) = else_case {
        s.fill(file_id, element_id);
    }
}

fn fill_while(
    meta: &mut Meta,
    cond: &mut Expression,
    stmt: &mut Statement,
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    cond.fill(file_id, element_id);
    stmt.fill(file_id, element_id);
}

fn fill_return(meta: &mut Meta, value: &mut Expression, file_id: usize, element_id: &mut usize) {
    meta.set_file_id(file_id);
    value.fill(file_id, element_id);
}

fn fill_initialization(
    meta: &mut Meta,
    initializations: &mut [Statement],
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    for init in initializations {
        init.fill(file_id, element_id);
    }
}

fn fill_declaration(
    meta: &mut Meta,
    dimensions: &mut [Expression],
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    for d in dimensions {
        d.fill(file_id, element_id);
    }
}

fn fill_substitution(
    meta: &mut Meta,
    access: &mut [Access],
    rhe: &mut Expression,
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    rhe.fill(file_id, element_id);
    for a in access {
        if let Access::ArrayAccess(e) = a {
            e.fill(file_id, element_id);
        }
    }
}

fn fill_multi_substitution(
    meta: &mut Meta,
    lhe: &mut Expression,
    rhe: &mut Expression,
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    rhe.fill(file_id, element_id);
    lhe.fill(file_id, element_id);
}

fn fill_constraint_equality(
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

fn fill_log_call(
    meta: &mut Meta,
    args: &mut Vec<LogArgument>,
    file_id: usize,
    element_id: &mut usize,
) {
    meta.set_file_id(file_id);
    for arg in args {
        if let LogArgument::LogExp(e) = arg {
            e.fill(file_id, element_id);
        }
    }
}

fn fill_block(meta: &mut Meta, stmts: &mut [Statement], file_id: usize, element_id: &mut usize) {
    meta.set_file_id(file_id);
    for s in stmts {
        s.fill(file_id, element_id);
    }
}

fn fill_assert(meta: &mut Meta, arg: &mut Expression, file_id: usize, element_id: &mut usize) {
    meta.set_file_id(file_id);
    arg.fill(file_id, element_id);
}

impl Debug for Statement {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        use Statement::*;
        match self {
            IfThenElse { .. } => write!(f, "Statement::IfThenElse"),
            While { .. } => write!(f, "Statement::While"),
            Return { .. } => write!(f, "Statement::Return"),
            Declaration { .. } => write!(f, "Statement::Declaration"),
            Substitution { .. } => write!(f, "Statement::Substitution"),
            MultiSubstitution { .. } => write!(f, "Statement::MultiSubstitution"),
            LogCall { .. } => write!(f, "Statement::LogCall"),
            Block { .. } => write!(f, "Statement::Block"),
            Assert { .. } => write!(f, "Statement::Assert"),
            ConstraintEquality { .. } => write!(f, "Statement::ConstraintEquality"),
            InitializationBlock { .. } => write!(f, "Statement::InitializationBlock"),
        }
    }
}

impl Display for Statement {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        use Statement::*;
        match self {
            IfThenElse { cond, else_case, .. } => match else_case {
                Some(_) => write!(f, "if {cond} else"),
                None => write!(f, "if {cond}"),
            },
            While { cond, .. } => write!(f, "while {cond}"),
            Return { value, .. } => write!(f, "return {value}"),
            Declaration { name, xtype, .. } => write!(f, "{xtype} {name}"),
            Substitution { var, access, op, rhe, .. } => {
                write!(f, "{var}")?;
                for access in access {
                    write!(f, "{access}")?;
                }
                write!(f, " {op} {rhe}")
            }
            MultiSubstitution { lhe, op, rhe, .. } => write!(f, "{lhe} {op} {rhe}"),
            LogCall { args, .. } => write!(f, "log({})", vec_to_string(args)),
            Block { .. } => Ok(()),
            Assert { arg, .. } => write!(f, "assert({arg})"),
            ConstraintEquality { lhe, rhe, .. } => write!(f, "{lhe} === {rhe}"),
            InitializationBlock { .. } => Ok(()),
        }
    }
}

impl Display for AssignOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        use AssignOp::*;
        match self {
            AssignVar => write!(f, "="),
            AssignSignal => write!(f, "<--"),
            AssignConstraintSignal => write!(f, "<=="),
        }
    }
}

impl Display for VariableType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        use SignalType::*;
        use VariableType::*;
        match self {
            Var => write!(f, "var"),
            Signal(signal_type, tag_list) => {
                if matches!(signal_type, Intermediate) {
                    write!(f, "signal")?;
                } else {
                    write!(f, "signal {signal_type}")?;
                }
                if !tag_list.is_empty() {
                    write!(f, " {{{}}}", tag_list.join("}} {{"))
                } else {
                    Ok(())
                }
            }
            Component => write!(f, "component"),
            AnonymousComponent => write!(f, "anonymous component"),
        }
    }
}

impl Display for SignalType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        use SignalType::*;
        match self {
            Input => write!(f, "input"),
            Output => write!(f, "output"),
            Intermediate => write!(f, ""),
        }
    }
}

impl Display for LogArgument {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        use LogArgument::*;
        match self {
            LogStr(message) => write!(f, "{message}"),
            LogExp(value) => write!(f, "{value}"),
        }
    }
}

fn vec_to_string<T: ToString>(elems: &[T]) -> String {
    elems.iter().map(|arg| arg.to_string()).collect::<Vec<String>>().join(", ")
}
