use program_structure::ast::{AssignOp, Expression, ExpressionInfixOpcode, ExpressionPrefixOpcode, Statement};

pub trait ToString {
    fn to_string(&self) -> String;
}

impl ToString for Statement {
    fn to_string(&self) -> String {
        match self {
            Statement::IfThenElse { .. } => "if-then-else statement".to_string(),
            Statement::While { .. } => "while statement".to_string(),
            Statement::Return { .. } => "return statement".to_string(),
            Statement::InitializationBlock { .. } => "initialization block".to_string(),
            Statement::Declaration { name, .. } => format!("declaration of '{name}'"),
            Statement::Substitution { var, op, .. } => format!("{} '{var}'", &op.to_string()),
            Statement::ConstraintEquality { .. } => "constraint equality".to_string(),
            Statement::LogCall { .. } => "log call".to_string(),
            Statement::Block { .. } => "basic block".to_string(),
            Statement::Assert { .. } => "assert statement".to_string(),
        }
    }
}

impl ToString for Expression {
    fn to_string(&self) -> String {
        match self {
            Expression::InfixOp { infix_op, .. } => format!("{} expression", infix_op.to_string()),
            Expression::PrefixOp { prefix_op, .. } => format!("{} expression", prefix_op.to_string()),
            Expression::InlineSwitchOp { .. } => "inline switch expression".to_string(),
            Expression::Variable { name, .. } => format!("variable expression '{name}'"),
            Expression::Number ( _, value ) => format!("constant expression '{value}'"),
            Expression::Call { id, .. } => format!("call to '{id}'"),
            Expression::ArrayInLine { .. } => "inline array expression ".to_string(),
        }
    }
}

impl ToString for ExpressionInfixOpcode {
    fn to_string(&self) -> String {
        match self {
            ExpressionInfixOpcode::Mul => "mutliplication",
            ExpressionInfixOpcode::Div => "division",
            ExpressionInfixOpcode::Add => "addition",
            ExpressionInfixOpcode::Sub => "subtraction",
            ExpressionInfixOpcode::Pow => "power",
            ExpressionInfixOpcode::IntDiv => "integer division",
            ExpressionInfixOpcode::Mod => "modulo",
            ExpressionInfixOpcode::ShiftL => "left-shift",
            ExpressionInfixOpcode::ShiftR => "right-shift",
            ExpressionInfixOpcode::LesserEq => "less than or equal",
            ExpressionInfixOpcode::GreaterEq => "greater than or equal",
            ExpressionInfixOpcode::Lesser => "less than",
            ExpressionInfixOpcode::Greater => "greater than",
            ExpressionInfixOpcode::Eq => "equal",
            ExpressionInfixOpcode::NotEq => "not equal",
            ExpressionInfixOpcode::BoolOr => "boolean OR",
            ExpressionInfixOpcode::BoolAnd => "boolean AND",
            ExpressionInfixOpcode::BitOr => "bitwise OR",
            ExpressionInfixOpcode::BitAnd => "bitwise AND",
            ExpressionInfixOpcode::BitXor => "bitwise XOR",
        }
        .to_string()
    }
}

impl ToString for ExpressionPrefixOpcode {
    fn to_string(&self) -> String {
        match self {
            ExpressionPrefixOpcode::Sub => "additive inverse",
            ExpressionPrefixOpcode::BoolNot => "boolean NOT",
            ExpressionPrefixOpcode::Complement => "bitwise complement",
        }
        .to_string()
    }
}

impl ToString for AssignOp {
    fn to_string(&self) -> String {
        match self {
            AssignOp::AssignVar => "assignment to variable",
            AssignOp::AssignSignal => "assignment to signal",
            AssignOp::AssignConstraintSignal => "constraint assignment to signal"
        }
        .to_string()
    }
}
