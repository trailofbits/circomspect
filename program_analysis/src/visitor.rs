use log::debug;
use num_bigint_dig::BigInt;
use program_structure::program_library::function_data::{FunctionInfo, FunctionData};
use program_structure::program_library::template_data::{TemplateInfo, TemplateData};
use program_structure::ast::{Access, AssignOp, Expression, ExpressionInfixOpcode, ExpressionPrefixOpcode, Meta, Statement, VariableType};

use super::utils::ToString;

pub trait Visitor {
    fn visit_templates(&mut self, templates: &TemplateInfo) {
        for (name, template) in templates.iter() {
            self.visit_template(name, template);
        }
    }

    fn visit_template(&mut self, name: &str, template: &TemplateData) {
        debug!("visiting template '{name}'");
        self.visit_stmt(template.get_body());
    }

    fn visit_functions(&mut self, functions: &FunctionInfo) {
        for (name, function) in functions.iter() {
            self.visit_function(name, function);
        }
    }

    fn visit_function(&mut self, name: &str, function: &FunctionData) {
        debug!("visiting function '{name}'");
        self.visit_stmt(function.get_body());
    }

    fn visit_stmt(&mut self, stmt: &Statement) {
        debug!("visiting {}", stmt.to_string());
        match stmt {
            Statement::IfThenElse { meta, cond, if_case, else_case } =>
                self.visit_ite(meta, cond, if_case, else_case),
            Statement::While { meta, cond, stmt } =>
                self.visit_while(meta, cond, stmt),
            Statement::Return { meta, value } =>
                self.visit_return(meta, value),
            Statement::InitializationBlock { meta, xtype, initializations } =>
                self.visit_init_block(meta, xtype, initializations),
            Statement::Declaration { meta, xtype, name, dimensions, is_constant } =>
                self.visit_declaration(meta, xtype, name, dimensions, is_constant),
            Statement::Substitution { meta, var, access, op, rhe } =>
                self.visit_substitution(meta, var, access, op, rhe),
            Statement::ConstraintEquality { meta, lhe, rhe } =>
                self.visit_constraint_eq(meta, lhe, rhe),
            Statement::LogCall { meta, arg } =>
                self.visit_log_call(meta, arg),
            Statement::Block { meta, stmts } =>
                self.visit_block(meta, stmts),
            Statement::Assert { meta, arg } =>
                self.visit_assert(meta, arg),
        }
    }

    fn visit_expr(&mut self, expr: &Expression) {
        debug!("visiting {}", expr.to_string());
        match expr {
            Expression::InfixOp { meta, lhe, infix_op, rhe } =>
                self.visit_infix_op(meta, lhe, infix_op, rhe),
            Expression::PrefixOp { meta, prefix_op, rhe } =>
                self.visit_prefix_op(meta, prefix_op, rhe),
            Expression::InlineSwitchOp { meta, cond, if_true, if_false } =>
                self.visit_inline_switch_op(meta, cond, if_true, if_false),
            Expression::Variable { meta, name, access } =>
                self.visit_variable(meta, name, access),
            Expression::Number(meta, value) =>
                self.visit_number(meta, value),
            Expression::Call { meta, id, args } =>
                self.visit_call(meta, id, args),
            Expression::ArrayInLine { meta, values } =>
                self.visit_array_inline(meta, values),
        }
    }

    // Statement visitors.
    fn visit_ite(&mut self, _meta: &Meta, cond: &Expression, if_case: &Statement, else_case: &Option<Box<Statement>>) {
        // Default implementation does nothing.

        self.visit_expr(cond);
        self.visit_stmt(if_case);
        if let Some(else_case) = else_case {
            self.visit_stmt(else_case);
        }
    }

    fn visit_while(&mut self, _meta: &Meta, cond: &Expression, stmt: &Statement) {
        // Default implementation does nothing.

        self.visit_expr(cond);
        self.visit_stmt(stmt);
    }

    fn visit_return(&mut self, _meta: &Meta, value: &Expression) {
        // Default implementation does nothing.

        self.visit_expr(value);
    }

    fn visit_init_block(&mut self, _meta: &Meta, _xtype: &VariableType, initializations: &[Statement]) {
        // Default implementation does nothing.

        for init in initializations {
            self.visit_stmt(init);
        }
    }

    fn visit_declaration(&mut self, _meta: &Meta, _xtype: &VariableType, _name: &str, dimensions: &[Expression], _is_constant: &bool) {
        // Default implementation does nothing.

        for dim in dimensions {
            self.visit_expr(dim);
        }
    }

    fn visit_substitution(&mut self, _meta: &Meta, _var: &str, _access: &[Access], _op: &AssignOp, rhe: &Expression) {
        // Default implementation does nothing.

        self.visit_expr(rhe);
    }

    fn visit_constraint_eq(&mut self, _meta: &Meta, lhe: &Expression, rhe: &Expression) {
        // Default implementation does nothing.

        self.visit_expr(lhe);
        self.visit_expr(rhe);
    }

    fn visit_log_call(&mut self, _meta: &Meta, arg: &Expression) {
        // Default implementation does nothing.

        self.visit_expr(arg);
    }

    fn visit_block(&mut self, _meta: &Meta, stmts: &[Statement]) {
        // Default implementation does nothing.

        for stmt in stmts {
            self.visit_stmt(stmt);
        }
    }

    fn visit_assert(&mut self, _meta: &Meta, arg: &Expression) {
        // Default implementation does nothing.

        self.visit_expr(arg);
    }

    // Expression visitors.
    fn visit_infix_op(&mut self, _meta: &Meta, lhe: &Expression, _op: &ExpressionInfixOpcode, rhe: &Expression) {
        // Default implementation does nothing.

        self.visit_expr(lhe);
        self.visit_expr(rhe);
    }

    fn visit_prefix_op(&mut self, _meta: &Meta, _op: &ExpressionPrefixOpcode, rhe: &Expression) {
        // Default implementation does nothing.

        self.visit_expr(rhe);
    }

    fn visit_inline_switch_op(&mut self, _meta: &Meta, cond: &Expression, if_true: &Expression, if_false: &Expression) {
        // Default implementation does nothing.

        self.visit_expr(cond);
        self.visit_expr(if_true);
        self.visit_expr(if_false);
    }

    fn visit_variable(&mut self, _meta: &Meta, _name: &str, _access: &[Access]) {
        // Default implementation does nothing.
    }

    fn visit_number(&mut self, _meta: &Meta, _value: &BigInt) {
        // Default implementation does nothing.
    }

    fn visit_call(&mut self, _meta: &Meta, _id: &str, args: &[Expression]) {
        // Default implementation does nothing.

        for arg in args {
            self.visit_expr(arg);
        }
    }

    fn visit_array_inline(&mut self, _meta: &Meta, values: &[Expression]) {
        // Default implementation does nothing.

        for value in values {
            self.visit_expr(value);
        }
    }
}

