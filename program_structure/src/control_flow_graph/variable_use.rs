use crate::abstract_syntax_tree::ast::{AssignOp, Expression, Statement};
use std::collections::HashSet;

type VariableUse = HashSet<String>;

pub fn compute_variable_use(stmt: &mut Statement) {
    let mut variables_read = VariableUse::new();
    let mut variables_written = VariableUse::new();

    use AssignOp::*;
    use Statement::*;
    match stmt {
        IfThenElse { cond, .. } => {
            visit_expression(cond, &mut variables_read);
        }
        While { cond, .. } => {
            visit_expression(cond, &mut variables_read);
        }
        Return { value, .. } => {
            visit_expression(value, &mut variables_read);
        }
        Declaration { .. } => {}
        Substitution { var, op, rhe, .. } => {
            // We currently only consider variable writes.
            if matches!(op, AssignVar) {
                variables_written.insert(var.clone());
                visit_expression(rhe, &mut variables_read);
            }
        }
        LogCall { arg, .. } => {
            visit_expression(arg, &mut variables_read);
        }
        Block { .. } => {}
        Assert { arg, .. } => {
            visit_expression(arg, &mut variables_read);
        }
        ConstraintEquality { lhe, rhe, .. } => {
            visit_expression(lhe, &mut variables_read);
            visit_expression(rhe, &mut variables_read);
        }
        InitializationBlock { .. } => {}
    }
    stmt.get_mut_meta()
        .get_mut_variable_knowledge()
        .set_variables_read(&variables_read);
    stmt.get_mut_meta()
        .get_mut_variable_knowledge()
        .set_variables_written(&variables_written);
}

fn visit_expression(expr: &Expression, vars: &mut VariableUse) {
    use Expression::*;
    match expr {
        InfixOp { lhe, rhe, .. } => {
            visit_expression(lhe, vars);
            visit_expression(rhe, vars);
        }
        PrefixOp { rhe, .. } => {
            visit_expression(rhe, vars);
        }
        InlineSwitchOp {
            cond,
            if_true,
            if_false,
            ..
        } => {
            visit_expression(cond, vars);
            visit_expression(if_true, vars);
            visit_expression(if_false, vars);
        }
        Variable { .. } => {
            vars.insert(expr.to_string());
        }
        SSAVariable { .. } => {
            vars.insert(expr.to_string());
        }
        Number(_, _) => {}
        Call { args, .. } => {
            for arg in args {
                visit_expression(arg, vars);
            }
        }
        ArrayInLine { values, .. } => {
            for value in values {
                visit_expression(value, vars);
            }
        }
        Phi { args, .. } => {
            for arg in args {
                visit_expression(arg, vars);
            }
        }
    }
}
