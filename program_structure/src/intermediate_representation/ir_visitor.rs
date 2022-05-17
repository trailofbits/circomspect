use std::collections::HashMap;

use super::ir::{Expression, ExpressionType, Statement, StatementType};

type StatementVisitor<Environment> = Box<dyn Fn(&Statement, &mut Environment)>;
type ExpressionVisitor<Environment> = Box<dyn Fn(&Expression, &mut Environment)>;

type MutStatementVisitor<Environment> = Box<dyn Fn(&mut Statement, &mut Environment)>;
type MutExpressionVisitor<Environment> = Box<dyn Fn(&mut Expression, &mut Environment)>;

pub enum Traversal {
    PreOrder,
    PostOrder,
}

pub struct Visitor<Environment> {
    order: Traversal,
    stmt_visitors: HashMap<StatementType, StatementVisitor<Environment>>,
    expr_visitors: HashMap<ExpressionType, ExpressionVisitor<Environment>>,
    mut_stmt_visitors: HashMap<StatementType, MutStatementVisitor<Environment>>,
    mut_expr_visitors: HashMap<ExpressionType, MutExpressionVisitor<Environment>>,
}

// Implementation of statement visitors.
impl<Environment> Visitor<Environment> {
    pub fn new(order: Traversal) -> Self {
        Self {
            order,
            stmt_visitors: HashMap::new(),
            expr_visitors: HashMap::new(),
            mut_stmt_visitors: HashMap::new(),
            mut_expr_visitors: HashMap::new(),
        }
    }

    pub fn visit_statement(&self, stmt: &Statement, env: &mut Environment) {
        use Statement::*;
        // Visit current node if we are traversing the AST in pre-order.
        if let (Traversal::PreOrder, Some(visitor)) = (self.order, self.get_statement_visitor(stmt))
        {
            visitor(stmt, env);
        }
        // Visit children.
        match stmt {
            IfThenElse { cond } => self.visit_ite(stmt, env),
            Return { .. } => self.visit_return(stmt, env),
            Declaration { .. } => self.visit_declaration(stmt, env),
            Substitution { .. } => self.visit_substitution(stmt, env),
            ConstraintEquality { .. } => self.visit_constraint_eq(stmt, env),
            LogCall { .. } => self.visit_log_call(stmt, env),
            Assert { .. } => self.visit_assert(stmt, env),
        }
        // Visit current node if we are traversing the AST in post-order.
        if let (Traversal::PostOrder, Some(visitor)) =
            (self.order, self.get_statement_visitor(stmt))
        {
            visitor(stmt, env);
        }
    }

    pub fn visit_statement_mut(&self, stmt: &mut Statement, env: &mut Environment) {
        use Statement::*;
        // Visit current node if we are traversing the AST in pre-order.
        if let (Traversal::PreOrder, Some(visitor)) =
            (self.order, self.get_mut_statement_visitor(stmt))
        {
            visitor(stmt, env);
        }
        // Visit children.
        match stmt {
            IfThenElse { .. } => self.visit_ite_mut(stmt, env),
            Return { .. } => self.visit_return_mut(stmt, env),
            Declaration { .. } => self.visit_declaration_mut(stmt, env),
            Substitution { .. } => self.visit_substitution_mut(stmt, env),
            ConstraintEquality { .. } => self.visit_constraint_eq_mut(stmt, env),
            LogCall { .. } => self.visit_log_call_mut(stmt, env),
            Assert { .. } => self.visit_assert_mut(stmt, env),
        }
        // Visit current node if we are traversing the AST in post-order.
        if let (Traversal::PostOrder, Some(visitor)) =
            (self.order, self.get_mut_statement_visitor(stmt))
        {
            visitor(stmt, env);
        }
    }

    fn visit_ite(&self, stmt: &Statement, env: &mut Environment) {
        use Statement::*;
        let IfThenElse { cond, .. } = stmt;
        self.visit_expression(cond, env);
    }

    fn visit_ite_mut(&self, stmt: &mut Statement, env: &mut Environment) {
        use Statement::*;
        let IfThenElse { cond, .. } = stmt;
        self.visit_expression_mut(cond, env);
    }

    fn visit_return(&self, stmt: &Statement, env: &mut Environment) {
        use Statement::*;
        let Return { value, .. } = stmt;
        self.visit_expression(value, env);
    }

    fn visit_return_mut(&self, stmt: &mut Statement, env: &mut Environment) {
        use Statement::*;
        let Return { value, .. } = stmt;
        self.visit_expression_mut(value, env);
    }

    fn visit_declaration(&self, stmt: &Statement, env: &mut Environment) {}

    fn visit_declaration_mut(&self, stmt: &mut Statement, env: &mut Environment) {}

    fn visit_substitution(&self, stmt: &Statement, env: &mut Environment) {
        use Statement::*;
        let Substitution { rhe, .. } = stmt;
        self.visit_expression(rhe, env);
    }

    fn visit_substitution_mut(&self, stmt: &mut Statement, env: &mut Environment) {
        use Statement::*;
        let Substitution { rhe, .. } = stmt;
        self.visit_expression_mut(rhe, env);
    }

    fn visit_constraint_eq(&self, stmt: &Statement, env: &mut Environment) {
        use Statement::*;
        let ConstraintEquality { lhe, rhe, .. } = stmt;
        self.visit_expression(lhe, env);
        self.visit_expression(rhe, env);
    }

    fn visit_constraint_eq_mut(&self, stmt: &mut Statement, env: &mut Environment) {
        use Statement::*;
        let ConstraintEquality { lhe, rhe, .. } = stmt;
        self.visit_expression_mut(lhe, env);
        self.visit_expression_mut(rhe, env);
    }

    fn visit_log_call(&self, stmt: &Statement, env: &mut Environment) {
        use Statement::*;
        let LogCall { arg, .. } = stmt;
        self.visit_expression(arg, env);
    }

    fn visit_log_call_mut(&self, stmt: &mut Statement, env: &mut Environment) {
        use Statement::*;
        let LogCall { arg, .. } = stmt;
        self.visit_expression_mut(arg, env);
    }

    fn visit_assert(&self, stmt: &Statement, env: &mut Environment) {
        use Statement::*;
        let Assert { arg, .. } = stmt;
        self.visit_expression(arg, env);
    }

    fn visit_assert_mut(&self, stmt: &mut Statement, env: &mut Environment) {
        use Statement::*;
        let Assert { arg, .. } = stmt;
        self.visit_expression_mut(arg, env);
    }
}

// Implementation of expression visitors.
impl<Environment> Visitor<Environment> {
    pub fn visit_expression(&self, expr: &Expression, env: &mut Environment) {
        use Expression::*;
        // Visit current node if we are traversing the AST in pre-order.
        if matches!(self.order, Traversal::PreOrder) {
            self.get_expression_visitor(expr).map(|f| f(expr, env));
        }
        // Visit children.
        match expr {
            InfixOp { .. } => self.visit_infix_op(expr, env),
            PrefixOp { .. } => self.visit_prefix_op(expr, env),
            InlineSwitchOp { .. } => self.visit_inline_switch_op(expr, env),
            Variable { .. } => self.visit_variable(expr, env),
            Signal { .. } => self.visit_signal(expr, env),
            Component { .. } => self.visit_component(expr, env),
            Number(_, _) => self.visit_number(expr, env),
            Call { .. } => self.visit_call(expr, env),
            ArrayInLine { .. } => self.visit_array_inline(expr, env),
            Phi { .. } => self.visit_phi(expr, env),
        }
        // Visit current node if we are traversing the AST in post-order.
        if matches!(self.order, Traversal::PostOrder) {
            self.get_expression_visitor(expr).map(|f| f(expr, env));
        }
    }

    pub fn visit_expression_mut(&self, expr: &mut Expression, env: &mut Environment) {
        use Expression::*;
        // Visit current node if we are traversing the AST in pre-order.
        if matches!(self.order, Traversal::PreOrder) {
            self.get_mut_expression_visitor(expr).map(|f| f(expr, env));
        }
        // Visit children.
        match expr {
            InfixOp { .. } => self.visit_infix_op_mut(expr, env),
            PrefixOp { .. } => self.visit_prefix_op_mut(expr, env),
            InlineSwitchOp { .. } => self.visit_inline_switch_op_mut(expr, env),
            Variable { .. } => self.visit_variable_mut(expr, env),
            Signal { .. } => self.visit_signal_mut(expr, env),
            Component { .. } => self.visit_component_mut(expr, env),
            Number(_, _) => self.visit_number_mut(expr, env),
            Call { .. } => self.visit_call_mut(expr, env),
            ArrayInLine { .. } => self.visit_array_inline_mut(expr, env),
            Phi { .. } => self.visit_phi_mut(expr, env),
        }
        // Visit current node if we are traversing the AST in post-order.
        if matches!(self.order, Traversal::PostOrder) {
            self.get_mut_expression_visitor(expr).map(|f| f(expr, env));
        }
    }
}

// Implementation of custom visitor registration.
impl<Environment> Visitor<Environment> {
    pub fn on_statement(
        &mut self,
        stmt_type: StatementType,
        visitor: impl Fn(&Statement, &mut Environment) + 'static,
    ) -> Self {
        self.stmt_visitors.insert(stmt_type, Box::new(visitor));
        *self
    }

    pub fn on_expression(
        &mut self,
        expr_type: ExpressionType,
        visitor: impl Fn(&Expression, &mut Environment) + 'static,
    ) -> Self {
        self.expr_visitors.insert(expr_type, Box::new(visitor));
        *self
    }

    pub fn on_statement_mut(
        &mut self,
        stmt_type: StatementType,
        visitor: impl Fn(&mut Statement, &mut Environment) + 'static,
    ) -> Self {
        self.mut_stmt_visitors.insert(stmt_type, Box::new(visitor));
        *self
    }

    pub fn on_expression_mut(
        &mut self,
        expr_type: ExpressionType,
        visitor: impl Fn(&mut Expression, &mut Environment) + 'static,
    ) -> Self {
        self.mut_expr_visitors.insert(expr_type, Box::new(visitor));
        *self
    }

    fn get_statement_visitor(&self, stmt: &Statement) -> Option<&StatementVisitor<Environment>> {
        self.stmt_visitors.get(&stmt.get_type())
    }
    fn get_expression_visitor(&self, expr: &Expression) -> Option<&ExpressionVisitor<Environment>> {
        self.expr_visitors.get(&expr.get_type())
    }
    fn get_mut_statement_visitor(
        &self,
        stmt: &Statement,
    ) -> Option<&MutStatementVisitor<Environment>> {
        self.mut_stmt_visitors.get(&stmt.get_type())
    }
    fn get_mut_expression_visitor(
        &self,
        expr: &Expression,
    ) -> Option<&MutExpressionVisitor<Environment>> {
        self.mut_expr_visitors.get(&expr.get_type())
    }
}
