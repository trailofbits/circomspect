use crate::ast::{self, LogArgument};
use crate::report::ReportCollection;

use crate::ir;
use crate::ir::declarations::{Declaration, Declarations};
use crate::ir::errors::{IRError, IRResult};
use crate::nonempty_vec::NonEmptyVec;

/// The `TryLift` trait is used to lift an AST node to an IR node. This may fail
/// and produce an error. Even if the operation succeeds it may produce warnings
/// which in this case are added to the report collection.
pub(crate) trait TryLift<Context> {
    type IR;
    type Error;

    /// Generate a corresponding IR node of type `Self::IR` from an AST node.
    fn try_lift(
        &self,
        context: Context,
        reports: &mut ReportCollection,
    ) -> Result<Self::IR, Self::Error>;
}

#[derive(Default)]
pub(crate) struct LiftingEnvironment {
    /// Tracks all variable declarations.
    declarations: Declarations,
}

impl LiftingEnvironment {
    #[must_use]
    pub fn new() -> LiftingEnvironment {
        LiftingEnvironment::default()
    }

    pub fn add_declaration(&mut self, declaration: &Declaration) {
        self.declarations.add_declaration(declaration);
    }
}

impl From<LiftingEnvironment> for Declarations {
    fn from(env: LiftingEnvironment) -> Declarations {
        env.declarations
    }
}

// Attempt to convert an AST statement into an IR statement. This will fail on
// statements that need to be handled manually (like `While`, `IfThenElse`, and
// `MultiSubstitution`), as well as statements that have no direct IR
// counterparts (like `Declaration`, `Block`, and `InitializationBlock`).
impl TryLift<()> for ast::Statement {
    type IR = ir::Statement;
    type Error = IRError;

    fn try_lift(&self, _: (), reports: &mut ReportCollection) -> IRResult<Self::IR> {
        match self {
            ast::Statement::Return { meta, value } => Ok(ir::Statement::Return {
                meta: meta.try_lift((), reports)?,
                value: value.try_lift((), reports)?,
            }),
            ast::Statement::Substitution { meta, var, op, rhe, access } => {
                // If this is an array or component signal assignment (i.e. when access
                // is non-empty), the RHS is lifted to an `Update` expression.
                let rhe = if access.is_empty() {
                    rhe.try_lift((), reports)?
                } else {
                    ir::Expression::Update {
                        meta: meta.try_lift((), reports)?,
                        var: var.try_lift(meta, reports)?,
                        access: access
                            .iter()
                            .map(|access| access.try_lift((), reports))
                            .collect::<IRResult<Vec<ir::AccessType>>>()?,
                        rhe: Box::new(rhe.try_lift((), reports)?),
                    }
                };
                Ok(ir::Statement::Substitution {
                    meta: meta.try_lift((), reports)?,
                    var: var.try_lift(meta, reports)?,
                    op: op.try_lift((), reports)?,
                    rhe,
                })
            }
            ast::Statement::ConstraintEquality { meta, lhe, rhe } => {
                Ok(ir::Statement::ConstraintEquality {
                    meta: meta.try_lift((), reports)?,
                    lhe: lhe.try_lift((), reports)?,
                    rhe: rhe.try_lift((), reports)?,
                })
            }
            ast::Statement::LogCall { meta, args } => Ok(ir::Statement::LogCall {
                meta: meta.try_lift((), reports)?,
                args: args
                    .iter()
                    .map(|arg| arg.try_lift((), reports))
                    .collect::<IRResult<Vec<_>>>()?,
            }),
            ast::Statement::Assert { meta, arg } => Ok(ir::Statement::Assert {
                meta: meta.try_lift((), reports)?,
                arg: arg.try_lift((), reports)?,
            }),
            ast::Statement::Declaration { meta, xtype, name, dimensions, .. } => {
                Ok(ir::Statement::Declaration {
                    meta: meta.try_lift((), reports)?,
                    names: NonEmptyVec::new(name.try_lift(meta, reports)?),
                    var_type: xtype.try_lift((), reports)?,
                    dimensions: dimensions
                        .iter()
                        .map(|size| size.try_lift((), reports))
                        .collect::<IRResult<Vec<_>>>()?,
                })
            }
            ast::Statement::Block { .. }
            | ast::Statement::While { .. }
            | ast::Statement::IfThenElse { .. }
            | ast::Statement::MultiSubstitution { .. }
            | ast::Statement::InitializationBlock { .. } => {
                // These need to be handled by the caller.
                panic!("failed to convert AST statement to IR")
            }
        }
    }
}

// Attempt to convert an AST expression to an IR expression. This will fail on
// expressions that need to be handled directly by the caller (like `Tuple` and
// `AnonymousComponent`).
impl TryLift<()> for ast::Expression {
    type IR = ir::Expression;
    type Error = IRError;

    fn try_lift(&self, _: (), reports: &mut ReportCollection) -> IRResult<Self::IR> {
        match self {
            ast::Expression::InfixOp { meta, lhe, infix_op, rhe } => Ok(ir::Expression::InfixOp {
                meta: meta.try_lift((), reports)?,
                lhe: Box::new(lhe.try_lift((), reports)?),
                infix_op: infix_op.try_lift((), reports)?,
                rhe: Box::new(rhe.try_lift((), reports)?),
            }),
            ast::Expression::PrefixOp { meta, prefix_op, rhe } => Ok(ir::Expression::PrefixOp {
                meta: meta.try_lift((), reports)?,
                prefix_op: prefix_op.try_lift((), reports)?,
                rhe: Box::new(rhe.try_lift((), reports)?),
            }),
            ast::Expression::InlineSwitchOp { meta, cond, if_true, if_false } => {
                Ok(ir::Expression::SwitchOp {
                    meta: meta.try_lift((), reports)?,
                    cond: Box::new(cond.try_lift((), reports)?),
                    if_true: Box::new(if_true.try_lift((), reports)?),
                    if_false: Box::new(if_false.try_lift((), reports)?),
                })
            }
            ast::Expression::Variable { meta, name, access } => {
                if access.is_empty() {
                    Ok(ir::Expression::Variable {
                        meta: meta.try_lift((), reports)?,
                        name: name.try_lift(meta, reports)?,
                    })
                } else {
                    Ok(ir::Expression::Access {
                        meta: meta.try_lift((), reports)?,
                        var: name.try_lift(meta, reports)?,
                        access: access
                            .iter()
                            .map(|access| access.try_lift((), reports))
                            .collect::<IRResult<Vec<ir::AccessType>>>()?,
                    })
                }
            }
            ast::Expression::Number(meta, value) => {
                Ok(ir::Expression::Number(meta.try_lift((), reports)?, value.clone()))
            }
            ast::Expression::Call { meta, id, args } => Ok(ir::Expression::Call {
                meta: meta.try_lift((), reports)?,
                name: id.clone(),
                args: args
                    .iter()
                    .map(|arg| arg.try_lift((), reports))
                    .collect::<IRResult<Vec<ir::Expression>>>()?,
            }),
            ast::Expression::ArrayInLine { meta, values } => Ok(ir::Expression::InlineArray {
                meta: meta.try_lift((), reports)?,
                values: values
                    .iter()
                    .map(|value| value.try_lift((), reports))
                    .collect::<IRResult<Vec<ir::Expression>>>()?,
            }),
            // TODO: We currently treat `ParallelOp` as transparent and simply
            // lift the underlying expression. Should this be added to the IR?
            ast::Expression::ParallelOp { rhe, .. } => rhe.try_lift((), reports),
            ast::Expression::Tuple { .. } | ast::Expression::AnonymousComponent { .. } => {
                // These need to be handled by the caller.
                panic!("failed to convert AST expression to IR")
            }
        }
    }
}

// Convert AST metadata to IR metadata. (This will always succeed.)
impl TryLift<()> for ast::Meta {
    type IR = ir::Meta;
    type Error = IRError;

    fn try_lift(&self, _: (), _: &mut ReportCollection) -> IRResult<Self::IR> {
        Ok(ir::Meta::new(&self.location, &self.file_id))
    }
}

// Convert an AST variable type to an IR type. (This will always succeed.)
impl TryLift<()> for ast::VariableType {
    type IR = ir::VariableType;
    type Error = IRError;

    fn try_lift(&self, _: (), reports: &mut ReportCollection) -> IRResult<Self::IR> {
        match self {
            ast::VariableType::Var => Ok(ir::VariableType::Local),
            ast::VariableType::Component => Ok(ir::VariableType::Component),
            ast::VariableType::AnonymousComponent => Ok(ir::VariableType::AnonymousComponent),
            ast::VariableType::Signal(signal_type, tag_list) => {
                Ok(ir::VariableType::Signal(signal_type.try_lift((), reports)?, tag_list.clone()))
            }
        }
    }
}

// Convert an AST signal type to an IR signal type. (This will always succeed.)
impl TryLift<()> for ast::SignalType {
    type IR = ir::SignalType;
    type Error = IRError;

    fn try_lift(&self, _: (), _: &mut ReportCollection) -> IRResult<Self::IR> {
        match self {
            ast::SignalType::Input => Ok(ir::SignalType::Input),
            ast::SignalType::Output => Ok(ir::SignalType::Output),
            ast::SignalType::Intermediate => Ok(ir::SignalType::Intermediate),
        }
    }
}

// Attempt to convert a string to an IR variable name.
impl TryLift<&ast::Meta> for String {
    type IR = ir::VariableName;
    type Error = IRError;

    fn try_lift(&self, meta: &ast::Meta, _: &mut ReportCollection) -> IRResult<Self::IR> {
        // We assume that the input string uses '.' to separate the name from the suffix.
        let tokens: Vec<_> = self.split('.').collect();
        match tokens.len() {
            1 => Ok(ir::VariableName::from_string(tokens[0])),
            2 => Ok(ir::VariableName::from_string(tokens[0]).with_suffix(tokens[1])),
            // Either the original name from the AST contains `.`, or the suffix
            // added when ensuring uniqueness contains `.`. Neither case should
            // occur, so we return an error here instead of producing a report.
            _ => Err(IRError::InvalidVariableNameError {
                name: self.clone(),
                file_id: meta.file_id,
                file_location: meta.location.clone(),
            }),
        }
    }
}

// Convert an AST access to an IR access. (This will always succeed.)
impl TryLift<()> for ast::Access {
    type IR = ir::AccessType;
    type Error = IRError;

    fn try_lift(&self, _: (), reports: &mut ReportCollection) -> IRResult<Self::IR> {
        match self {
            ast::Access::ArrayAccess(expr) => {
                Ok(ir::AccessType::ArrayAccess(Box::new(expr.try_lift((), reports)?)))
            }
            ast::Access::ComponentAccess(s) => Ok(ir::AccessType::ComponentAccess(s.clone())),
        }
    }
}

// Convert an AST assignment to an IR assignment. (This will always succeed.)
impl TryLift<()> for ast::AssignOp {
    type IR = ir::AssignOp;
    type Error = IRError;

    fn try_lift(&self, _: (), _: &mut ReportCollection) -> IRResult<Self::IR> {
        match self {
            ast::AssignOp::AssignSignal => Ok(ir::AssignOp::AssignSignal),
            ast::AssignOp::AssignVar => Ok(ir::AssignOp::AssignLocalOrComponent),
            ast::AssignOp::AssignConstraintSignal => Ok(ir::AssignOp::AssignConstraintSignal),
        }
    }
}

// Convert an AST opcode to an IR opcode. (This will always succeed.)
impl TryLift<()> for ast::ExpressionPrefixOpcode {
    type IR = ir::ExpressionPrefixOpcode;
    type Error = IRError;

    fn try_lift(&self, _: (), _: &mut ReportCollection) -> IRResult<Self::IR> {
        match self {
            ast::ExpressionPrefixOpcode::Sub => Ok(ir::ExpressionPrefixOpcode::Sub),
            ast::ExpressionPrefixOpcode::BoolNot => Ok(ir::ExpressionPrefixOpcode::BoolNot),
            ast::ExpressionPrefixOpcode::Complement => Ok(ir::ExpressionPrefixOpcode::Complement),
        }
    }
}

// Convert an AST opcode to an IR opcode. (This will always succeed.)
impl TryLift<()> for ast::ExpressionInfixOpcode {
    type IR = ir::ExpressionInfixOpcode;
    type Error = IRError;

    fn try_lift(&self, _: (), _: &mut ReportCollection) -> IRResult<Self::IR> {
        match self {
            ast::ExpressionInfixOpcode::Mul => Ok(ir::ExpressionInfixOpcode::Mul),
            ast::ExpressionInfixOpcode::Div => Ok(ir::ExpressionInfixOpcode::Div),
            ast::ExpressionInfixOpcode::Add => Ok(ir::ExpressionInfixOpcode::Add),
            ast::ExpressionInfixOpcode::Sub => Ok(ir::ExpressionInfixOpcode::Sub),
            ast::ExpressionInfixOpcode::Pow => Ok(ir::ExpressionInfixOpcode::Pow),
            ast::ExpressionInfixOpcode::IntDiv => Ok(ir::ExpressionInfixOpcode::IntDiv),
            ast::ExpressionInfixOpcode::Mod => Ok(ir::ExpressionInfixOpcode::Mod),
            ast::ExpressionInfixOpcode::ShiftL => Ok(ir::ExpressionInfixOpcode::ShiftL),
            ast::ExpressionInfixOpcode::ShiftR => Ok(ir::ExpressionInfixOpcode::ShiftR),
            ast::ExpressionInfixOpcode::LesserEq => Ok(ir::ExpressionInfixOpcode::LesserEq),
            ast::ExpressionInfixOpcode::GreaterEq => Ok(ir::ExpressionInfixOpcode::GreaterEq),
            ast::ExpressionInfixOpcode::Lesser => Ok(ir::ExpressionInfixOpcode::Lesser),
            ast::ExpressionInfixOpcode::Greater => Ok(ir::ExpressionInfixOpcode::Greater),
            ast::ExpressionInfixOpcode::Eq => Ok(ir::ExpressionInfixOpcode::Eq),
            ast::ExpressionInfixOpcode::NotEq => Ok(ir::ExpressionInfixOpcode::NotEq),
            ast::ExpressionInfixOpcode::BoolOr => Ok(ir::ExpressionInfixOpcode::BoolOr),
            ast::ExpressionInfixOpcode::BoolAnd => Ok(ir::ExpressionInfixOpcode::BoolAnd),
            ast::ExpressionInfixOpcode::BitOr => Ok(ir::ExpressionInfixOpcode::BitOr),
            ast::ExpressionInfixOpcode::BitAnd => Ok(ir::ExpressionInfixOpcode::BitAnd),
            ast::ExpressionInfixOpcode::BitXor => Ok(ir::ExpressionInfixOpcode::BitXor),
        }
    }
}

impl TryLift<()> for LogArgument {
    type IR = ir::LogArgument;
    type Error = IRError;

    fn try_lift(&self, _: (), reports: &mut ReportCollection) -> IRResult<Self::IR> {
        match self {
            ast::LogArgument::LogStr(message) => Ok(ir::LogArgument::String(message.clone())),
            ast::LogArgument::LogExp(value) => {
                Ok(ir::LogArgument::Expr(Box::new(value.try_lift((), reports)?)))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use crate::report::ReportCollection;

    use super::*;

    proptest! {
        #[test]
        fn variable_name_from_string(name in "[$_]*[a-zA-Z][a-zA-Z$_0-9]*") {
            let meta = ast::Meta::new(0, 1);
            let mut reports = ReportCollection::new();

            let var = name.try_lift(&meta, &mut reports).unwrap();
            assert!(var.suffix().is_none());
            assert!(var.version().is_none());
            assert!(reports.is_empty());
        }

        #[test]
        fn variable_name_with_suffix_from_string(name in "[$_]*[a-zA-Z][a-zA-Z$_0-9]*\\.[a-zA-Z$_0-9]*") {
            let meta = ast::Meta::new(0, 1);
            let mut reports = ReportCollection::new();

            let var = name.try_lift(&meta, &mut reports).unwrap();
            assert!(var.suffix().is_some());
            assert!(var.version().is_none());
            assert!(reports.is_empty());
        }

        #[test]
        fn variable_name_from_invalid_string(name in "[$_]*[a-zA-Z][a-zA-Z$_0-9]*\\.[a-zA-Z$_0-9]*\\.[a-zA-Z$_0-9]*") {
            let meta = ast::Meta::new(0, 1);
            let mut reports = ReportCollection::new();

            let result = name.try_lift(&meta, &mut reports);
            assert!(result.is_err());
            assert!(reports.is_empty());
        }
    }
}
