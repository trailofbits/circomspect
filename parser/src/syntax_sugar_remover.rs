use program_structure::ast::*;
use program_structure::statement_builders::{build_block, build_substitution};
use program_structure::report::{Report, ReportCollection};
use program_structure::expression_builders::{build_call, build_tuple, build_parallel_op};
use program_structure::file_definition::FileLibrary;
use program_structure::statement_builders::{
    build_declaration, build_log_call, build_assert, build_return, build_constraint_equality,
    build_initialization_block,
};
use program_structure::template_data::TemplateData;
use program_structure::function_data::FunctionData;
use std::collections::HashMap;
use num_bigint::BigInt;

use crate::errors::{AnonymousComponentError, TupleError};
use crate::syntax_sugar_traits::ContainsExpression;

/// This functions desugars all anonymous components and tuples.
#[must_use]
pub(crate) fn remove_syntactic_sugar(
    templates: &HashMap<String, TemplateData>,
    functions: &HashMap<String, FunctionData>,
    file_library: &FileLibrary,
    reports: &mut ReportCollection,
) -> (HashMap<String, TemplateData>, HashMap<String, FunctionData>) {
    // Remove anonymous components and tuples from templates.
    let mut new_templates = HashMap::new();
    for (name, template) in templates {
        let body = template.get_body().clone();
        let (new_body, declarations) =
            match remove_anonymous_from_statement(templates, file_library, body, &None) {
                Ok(result) => result,
                Err(report) => {
                    // If we encounter an error we simply report the error and continue.
                    // This means that the template is dropped and no more analysis is
                    // performed on it.
                    //
                    // TODO: If we want to do inter-procedural analysis we need to track
                    // removed templates.
                    reports.push(*report);
                    continue;
                }
            };
        if let Statement::Block { meta, mut stmts } = new_body {
            let (component_decs, variable_decs, mut substitutions) =
                separate_declarations_in_comp_var_subs(declarations);
            let mut init_block = vec![
                build_initialization_block(meta.clone(), VariableType::Var, variable_decs),
                build_initialization_block(meta.clone(), VariableType::Component, component_decs),
            ];
            init_block.append(&mut substitutions);
            init_block.append(&mut stmts);
            let new_body_with_inits = build_block(meta, init_block);
            let new_body = match remove_tuples_from_statement(new_body_with_inits) {
                Ok(result) => result,
                Err(report) => {
                    // If we encounter an error we simply report the error and continue.
                    // This means that the template is dropped and no more analysis is
                    // performed on it.
                    //
                    // TODO: If we want to do inter-procedural analysis we need to track
                    // removed templates.
                    reports.push(*report);
                    continue;
                }
            };
            let mut new_template = template.clone();
            *new_template.get_mut_body() = new_body;
            new_templates.insert(name.clone(), new_template);
        } else {
            unreachable!()
        }
    }

    // Drop any functions containing anonymous components or tuples.
    let mut new_functions = HashMap::new();
    for (name, function) in functions {
        let body = function.get_body();
        if body.contains_tuple(Some(reports)) {
            continue;
        }
        if body.contains_anonymous_component(Some(reports)) {
            continue;
        }
        new_functions.insert(name.clone(), function.clone());
    }
    (new_templates, new_functions)
}

fn remove_anonymous_from_statement(
    templates: &HashMap<String, TemplateData>,
    file_library: &FileLibrary,
    stmt: Statement,
    var_access: &Option<Expression>,
) -> Result<(Statement, Vec<Statement>), Box<Report>> {
    match stmt {
        Statement::MultiSubstitution { meta, lhe, op, rhe } => {
            if lhe.contains_anonymous_component(None) {
                return Err(AnonymousComponentError::boxed_report(
                    lhe.meta(),
                    "An anonymous component cannot occur as the left-hand side of an assignment",
                ));
            } else {
                let (mut stmts, declarations, new_rhe) =
                    remove_anonymous_from_expression(templates, file_library, rhe, var_access)?;
                let subs =
                    Statement::MultiSubstitution { meta: meta.clone(), lhe, op, rhe: new_rhe };
                let mut substs = Vec::new();
                if stmts.is_empty() {
                    Ok((subs, declarations))
                } else {
                    substs.append(&mut stmts);
                    substs.push(subs);
                    Ok((Statement::Block { meta, stmts: substs }, declarations))
                }
            }
        }
        Statement::IfThenElse { meta, cond, if_case, else_case } => {
            if cond.contains_anonymous_component(None) {
                Err(AnonymousComponentError::boxed_report(
                    &meta,
                    "Anonymous components cannot be used inside conditions.",
                ))
            } else {
                let (new_if_case, mut declarations) =
                    remove_anonymous_from_statement(templates, file_library, *if_case, var_access)?;
                match else_case {
                    Some(else_case) => {
                        let (new_else_case, mut new_declarations) =
                            remove_anonymous_from_statement(
                                templates,
                                file_library,
                                *else_case,
                                var_access,
                            )?;
                        declarations.append(&mut new_declarations);
                        Ok((
                            Statement::IfThenElse {
                                meta,
                                cond,
                                if_case: Box::new(new_if_case),
                                else_case: Some(Box::new(new_else_case)),
                            },
                            declarations,
                        ))
                    }
                    None => Ok((
                        Statement::IfThenElse {
                            meta,
                            cond,
                            if_case: Box::new(new_if_case),
                            else_case: None,
                        },
                        declarations,
                    )),
                }
            }
        }
        Statement::While { meta, cond, stmt } => {
            if cond.contains_anonymous_component(None) {
                return Err(AnonymousComponentError::boxed_report(
                    cond.meta(),
                    "Anonymous components cannot be used inside conditions.",
                ));
            } else {
                let id_var_while = "anon_var_".to_string()
                    + &file_library.get_line(meta.start, meta.get_file_id()).unwrap().to_string()
                    + "_"
                    + &meta.start.to_string();
                let var_access = Expression::Variable {
                    meta: meta.clone(),
                    name: id_var_while.clone(),
                    access: Vec::new(),
                };
                let mut declarations = vec![];
                let (new_stmt, mut new_declarations) = remove_anonymous_from_statement(
                    templates,
                    file_library,
                    *stmt,
                    &Some(var_access.clone()),
                )?;
                let boxed_stmt = if !new_declarations.is_empty() {
                    declarations.push(build_declaration(
                        meta.clone(),
                        VariableType::Var,
                        id_var_while.clone(),
                        Vec::new(),
                    ));
                    declarations.push(build_substitution(
                        meta.clone(),
                        id_var_while.clone(),
                        vec![],
                        AssignOp::AssignVar,
                        Expression::Number(meta.clone(), BigInt::from(0)),
                    ));
                    declarations.append(&mut new_declarations);
                    let next_access = Expression::InfixOp {
                        meta: meta.clone(),
                        infix_op: ExpressionInfixOpcode::Add,
                        lhe: Box::new(var_access),
                        rhe: Box::new(Expression::Number(meta.clone(), BigInt::from(1))),
                    };
                    let subs_access = Statement::Substitution {
                        meta: meta.clone(),
                        var: id_var_while,
                        access: Vec::new(),
                        op: AssignOp::AssignVar,
                        rhe: next_access,
                    };

                    let new_block =
                        Statement::Block { meta: meta.clone(), stmts: vec![new_stmt, subs_access] };
                    Box::new(new_block)
                } else {
                    Box::new(new_stmt)
                };

                Ok((Statement::While { meta, cond, stmt: boxed_stmt }, declarations))
            }
        }
        Statement::LogCall { meta, args } => {
            for arg in &args {
                if let program_structure::ast::LogArgument::LogExp(exp) = arg {
                    if exp.contains_anonymous_component(None) {
                        return Err(AnonymousComponentError::boxed_report(
                            &meta,
                            "An anonymous component cannot be used inside a log statement.",
                        ));
                    }
                }
            }
            Ok((build_log_call(meta, args), Vec::new()))
        }
        Statement::Assert { meta, arg } => Ok((build_assert(meta, arg), Vec::new())),
        Statement::Return { meta, value: arg } => {
            if arg.contains_anonymous_component(None) {
                Err(AnonymousComponentError::boxed_report(
                    &meta,
                    "An anonymous component cannot be used as a return value.",
                ))
            } else {
                Ok((build_return(meta, arg), Vec::new()))
            }
        }
        Statement::ConstraintEquality { meta, lhe, rhe } => {
            if lhe.contains_anonymous_component(None) || rhe.contains_anonymous_component(None) {
                Err(AnonymousComponentError::boxed_report(
                    &meta,
                    "Anonymous components cannot be used together with the constraint equality operator `===`.",
                ))
            } else {
                Ok((build_constraint_equality(meta, lhe, rhe), Vec::new()))
            }
        }
        Statement::Declaration { meta, xtype, name, dimensions, .. } => {
            for exp in dimensions.clone() {
                if exp.contains_anonymous_component(None) {
                    return Err(AnonymousComponentError::boxed_report(
                        exp.meta(),
                        "An anonymous component cannot be used to define the dimensions of an array.",
                    ));
                }
            }
            Ok((build_declaration(meta, xtype, name, dimensions), Vec::new()))
        }
        Statement::InitializationBlock { meta, xtype, initializations } => {
            let mut new_inits = Vec::new();
            let mut declarations = Vec::new();
            for stmt in initializations {
                let (stmt_ok, mut declaration) =
                    remove_anonymous_from_statement(templates, file_library, stmt, var_access)?;
                new_inits.push(stmt_ok);
                declarations.append(&mut declaration)
            }
            Ok((
                Statement::InitializationBlock { meta, xtype, initializations: new_inits },
                declarations,
            ))
        }
        Statement::Block { meta, stmts } => {
            let mut new_stmts = Vec::new();
            let mut declarations = Vec::new();
            for stmt in stmts {
                let (stmt_ok, mut declaration) =
                    remove_anonymous_from_statement(templates, file_library, stmt, var_access)?;
                new_stmts.push(stmt_ok);
                declarations.append(&mut declaration);
            }
            Ok((Statement::Block { meta, stmts: new_stmts }, declarations))
        }
        Statement::Substitution { meta, var, op, rhe, access } => {
            let (mut stmts, declarations, new_rhe) =
                remove_anonymous_from_expression(templates, file_library, rhe, var_access)?;
            let subs =
                Statement::Substitution { meta: meta.clone(), var, access, op, rhe: new_rhe };
            let mut substs = Vec::new();
            if stmts.is_empty() {
                Ok((subs, declarations))
            } else {
                substs.append(&mut stmts);
                substs.push(subs);
                Ok((Statement::Block { meta, stmts: substs }, declarations))
            }
        }
    }
}

// returns a block with the substitutions, the declarations and finally the output expression
fn remove_anonymous_from_expression(
    templates: &HashMap<String, TemplateData>,
    file_library: &FileLibrary,
    expr: Expression,
    var_access: &Option<Expression>, // in case the call is inside a loop, variable used to control the access
) -> Result<(Vec<Statement>, Vec<Statement>, Expression), Box<Report>> {
    use Expression::*;
    match expr.clone() {
        ArrayInLine { values, .. } => {
            for value in values {
                if value.contains_anonymous_component(None) {
                    return Err(AnonymousComponentError::boxed_report(
                        value.meta(),
                        "An anonymous component cannot be used to define the dimensions of an array.",
                    ));
                }
            }
            Ok((Vec::new(), Vec::new(), expr))
        }
        Number(_, _) => Ok((Vec::new(), Vec::new(), expr)),
        Variable { meta, .. } => {
            if expr.contains_anonymous_component(None) {
                return Err(AnonymousComponentError::boxed_report(
                    &meta,
                    "An anonymous component cannot be used to access an array.",
                ));
            }
            Ok((Vec::new(), Vec::new(), expr))
        }
        InfixOp { meta, lhe, rhe, .. } => {
            if lhe.contains_anonymous_component(None) || rhe.contains_anonymous_component(None) {
                return Err(AnonymousComponentError::boxed_report(
                    &meta,
                    "Anonymous components cannot be used in arithmetic or boolean expressions.",
                ));
            }
            Ok((Vec::new(), Vec::new(), expr))
        }
        PrefixOp { meta, rhe, .. } => {
            if rhe.contains_anonymous_component(None) {
                return Err(AnonymousComponentError::boxed_report(
                    &meta,
                    "Anonymous components cannot be used in arithmetic or boolean expressions.",
                ));
            }
            Ok((Vec::new(), Vec::new(), expr))
        }
        InlineSwitchOp { meta, cond, if_true, if_false } => {
            if cond.contains_anonymous_component(None)
                || if_true.contains_anonymous_component(None)
                || if_false.contains_anonymous_component(None)
            {
                return Err(AnonymousComponentError::boxed_report(
                    &meta,
                    "An anonymous component cannot be used inside an inline switch expression.",
                ));
            }
            Ok((Vec::new(), Vec::new(), expr))
        }
        Call { meta, args, .. } => {
            for value in args {
                if value.contains_anonymous_component(None) {
                    return Err(AnonymousComponentError::boxed_report(
                        &meta,
                        "An anonymous component cannot be used as an argument to a template call.",
                    ));
                }
            }
            Ok((Vec::new(), Vec::new(), expr))
        }
        AnonymousComponent { meta, id, params, signals, names, is_parallel } => {
            let template = templates.get(&id);
            let mut declarations = Vec::new();
            if template.is_none() {
                return Err(Box::new(
                    AnonymousComponentError::new(
                        Some(&meta),
                        &format!("The template `{id}` does not exist."),
                        Some(&format!("Unknown template `{id}` instantiated here.")),
                    )
                    .into_report(),
                ));
            }
            let mut i = 0;
            let mut seq_substs = Vec::new();
            let id_anon_temp = id.to_string()
                + "_"
                + &file_library.get_line(meta.start, meta.get_file_id()).unwrap().to_string()
                + "_"
                + &meta.start.to_string();
            if var_access.is_none() {
                declarations.push(build_declaration(
                    meta.clone(),
                    VariableType::Component,
                    id_anon_temp.clone(),
                    Vec::new(),
                ));
            } else {
                declarations.push(build_declaration(
                    meta.clone(),
                    VariableType::AnonymousComponent,
                    id_anon_temp.clone(),
                    vec![var_access.as_ref().unwrap().clone()],
                ));
            }
            let call = build_call(meta.clone(), id, params);
            if call.contains_anonymous_component(None) {
                return Err(AnonymousComponentError::boxed_report(
                    &meta,
                    "An anonymous component cannot be used as a argument to a template call.",
                ));
            }

            let exp_with_call =
                if is_parallel { build_parallel_op(meta.clone(), call) } else { call };
            let access = if var_access.is_none() {
                Vec::new()
            } else {
                vec![build_array_access(var_access.as_ref().unwrap().clone())]
            };
            let sub = build_substitution(
                meta.clone(),
                id_anon_temp.clone(),
                access,
                AssignOp::AssignVar,
                exp_with_call,
            );
            seq_substs.push(sub);
            let inputs = template.unwrap().get_declaration_inputs();
            let mut new_signals = Vec::new();
            let mut new_operators = Vec::new();
            if let Some(m) = names {
                let (operators, names): (Vec<AssignOp>, Vec<String>) = m.iter().cloned().unzip();
                for inp in inputs {
                    if !names.contains(&inp.0) {
                        return Err(AnonymousComponentError::boxed_report(
                            &meta,
                            &format!("The input signal `{}` is not assigned by the anonymous component call.", inp.0),
                        ));
                    } else {
                        let pos = names.iter().position(|r| *r == inp.0).unwrap();
                        new_signals.push(signals.get(pos).unwrap().clone());
                        new_operators.push(*operators.get(pos).unwrap());
                    }
                }
            } else {
                new_signals = signals.clone();
                for _ in 0..signals.len() {
                    new_operators.push(AssignOp::AssignConstraintSignal);
                }
            }
            if inputs.len() != new_signals.len() || inputs.len() != signals.len() {
                return Err(AnonymousComponentError::boxed_report(&meta, "The number of input arguments must be equal to the number of input signals of the template."));
            }
            for inp in inputs {
                let mut acc = if var_access.is_none() {
                    Vec::new()
                } else {
                    vec![build_array_access(var_access.as_ref().unwrap().clone())]
                };
                acc.push(Access::ComponentAccess(inp.0.clone()));
                let (mut stmts, mut new_declarations, new_expr) = remove_anonymous_from_expression(
                    templates,
                    file_library,
                    new_signals.get(i).unwrap().clone(),
                    var_access,
                )?;
                if new_expr.contains_anonymous_component(None) {
                    return Err(AnonymousComponentError::boxed_report(
                        new_expr.meta(),
                        "The inputs to an anonymous component cannot contain anonymous components.",
                    ));
                }
                seq_substs.append(&mut stmts);
                declarations.append(&mut new_declarations);
                let subs = Statement::Substitution {
                    meta: meta.clone(),
                    var: id_anon_temp.clone(),
                    access: acc,
                    op: *new_operators.get(i).unwrap(),
                    rhe: new_expr,
                };
                i += 1;
                seq_substs.push(subs);
            }
            let outputs = template.unwrap().get_declaration_outputs();
            if outputs.len() == 1 {
                let output = outputs[0].0.clone();
                let mut acc = if var_access.is_none() {
                    Vec::new()
                } else {
                    vec![build_array_access(var_access.as_ref().unwrap().clone())]
                };

                acc.push(Access::ComponentAccess(output));
                let out_exp =
                    Expression::Variable { meta: meta.clone(), name: id_anon_temp, access: acc };
                Ok((vec![Statement::Block { meta, stmts: seq_substs }], declarations, out_exp))
            } else {
                let mut new_values = Vec::new();
                for output in outputs {
                    let mut acc = if var_access.is_none() {
                        Vec::new()
                    } else {
                        vec![build_array_access(var_access.as_ref().unwrap().clone())]
                    };
                    acc.push(Access::ComponentAccess(output.0.clone()));
                    let out_exp = Expression::Variable {
                        meta: meta.clone(),
                        name: id_anon_temp.clone(),
                        access: acc,
                    };
                    new_values.push(out_exp);
                }
                let out_exp = Tuple { meta: meta.clone(), values: new_values };
                Ok((vec![Statement::Block { meta, stmts: seq_substs }], declarations, out_exp))
            }
        }
        Tuple { meta, values } => {
            let mut new_values = Vec::new();
            let mut new_stmts: Vec<Statement> = Vec::new();
            let mut declarations: Vec<Statement> = Vec::new();
            for val in values {
                let result =
                    remove_anonymous_from_expression(templates, file_library, val, var_access);
                match result {
                    Ok((mut stm, mut declaration, val2)) => {
                        new_stmts.append(&mut stm);
                        new_values.push(val2);
                        declarations.append(&mut declaration);
                    }
                    Err(er) => {
                        return Err(er);
                    }
                }
            }
            Ok((new_stmts, declarations, build_tuple(meta, new_values)))
        }
        ParallelOp { meta, rhe } => {
            if !rhe.is_call()
                && !rhe.is_anonymous_component()
                && rhe.contains_anonymous_component(None)
            {
                return Err(AnonymousComponentError::boxed_report(
                    &meta,
                    "Invalid use of the parallel operator together with an anonymous component.",
                ));
            } else if rhe.is_call() && rhe.contains_anonymous_component(None) {
                return Err(AnonymousComponentError::boxed_report(
                    &meta,
                    "An anonymous component cannot be used as a parameter in a template call.",
                ));
            } else if rhe.is_anonymous_component() {
                let rhe2 = rhe.make_anonymous_parallel();
                return remove_anonymous_from_expression(templates, file_library, rhe2, var_access);
            }
            Ok((Vec::new(), Vec::new(), expr))
        }
    }
}

fn separate_declarations_in_comp_var_subs(
    declarations: Vec<Statement>,
) -> (Vec<Statement>, Vec<Statement>, Vec<Statement>) {
    let mut components_dec = Vec::new();
    let mut variables_dec = Vec::new();
    let mut substitutions = Vec::new();
    for dec in declarations {
        if let Statement::Declaration { ref xtype, .. } = dec {
            if matches!(xtype, VariableType::Component | VariableType::AnonymousComponent) {
                components_dec.push(dec);
            } else if VariableType::Var.eq(xtype) {
                variables_dec.push(dec);
            } else {
                unreachable!();
            }
        } else if let Statement::Substitution { .. } = dec {
            substitutions.push(dec);
        } else {
            unreachable!();
        }
    }
    (components_dec, variables_dec, substitutions)
}

fn remove_tuples_from_statement(stmt: Statement) -> Result<Statement, Box<Report>> {
    match stmt {
        Statement::MultiSubstitution { meta, lhe, op, rhe } => {
            let new_lhe = remove_tuple_from_expression(lhe)?;
            let new_rhe = remove_tuple_from_expression(rhe)?;
            match (new_lhe, new_rhe) {
                (
                    Expression::Tuple { values: mut lhe_values, .. },
                    Expression::Tuple { values: mut rhe_values, .. },
                ) => {
                    if lhe_values.len() == rhe_values.len() {
                        let mut substs = Vec::new();
                        while !lhe_values.is_empty() {
                            let lhe = lhe_values.remove(0);
                            if let Expression::Variable { meta, name, access } = lhe {
                                let rhe = rhe_values.remove(0);
                                if name != "_" {
                                    substs.push(build_substitution(
                                        meta.clone(),
                                        name.clone(),
                                        access.to_vec(),
                                        op,
                                        rhe,
                                    ));
                                }
                            } else {
                                return Err(TupleError::boxed_report(&meta, "The elements of the destination tuple must be either signals or variables."));
                            }
                        }
                        Ok(build_block(meta, substs))
                    } else if !lhe_values.is_empty() {
                        Err(TupleError::boxed_report(
                            &meta,
                            "The two tuples do not have the same length.",
                        ))
                    } else {
                        Err(TupleError::boxed_report(
                            &meta,
                            "This expression must be the right-hand side of an assignment.",
                        ))
                    }
                }
                (lhe, rhe) => {
                    if lhe.is_tuple() || lhe.is_variable() {
                        return Err(TupleError::boxed_report(
                            rhe.meta(),
                            "This expression must be a tuple or an anonymous component.",
                        ));
                    } else {
                        return Err(TupleError::boxed_report(
                            lhe.meta(),
                            "This expression must be a tuple, a component, a signal or a variable.",
                        ));
                    }
                }
            }
        }
        Statement::IfThenElse { meta, cond, if_case, else_case } => {
            if cond.contains_tuple(None) {
                Err(TupleError::boxed_report(&meta, "Tuples cannot be used in conditions."))
            } else {
                let new_if_case = remove_tuples_from_statement(*if_case)?;
                match else_case {
                    Some(else_case) => {
                        let new_else_case = remove_tuples_from_statement(*else_case)?;
                        Ok(Statement::IfThenElse {
                            meta,
                            cond,
                            if_case: Box::new(new_if_case),
                            else_case: Some(Box::new(new_else_case)),
                        })
                    }
                    None => Ok(Statement::IfThenElse {
                        meta,
                        cond,
                        if_case: Box::new(new_if_case),
                        else_case: None,
                    }),
                }
            }
        }
        Statement::While { meta, cond, stmt } => {
            if cond.contains_tuple(None) {
                Err(TupleError::boxed_report(&meta, "Tuples cannot be used in conditions."))
            } else {
                let new_stmt = remove_tuples_from_statement(*stmt)?;
                Ok(Statement::While { meta, cond, stmt: Box::new(new_stmt) })
            }
        }
        Statement::LogCall { meta, args } => {
            let mut new_args = Vec::new();
            for arg in args {
                match arg {
                    LogArgument::LogStr(str) => {
                        new_args.push(LogArgument::LogStr(str));
                    }
                    LogArgument::LogExp(exp) => {
                        let mut sep_args = separate_tuple_for_log_call(vec![exp]);
                        new_args.append(&mut sep_args);
                    }
                }
            }
            Ok(build_log_call(meta, new_args))
        }
        Statement::Assert { meta, arg } => Ok(build_assert(meta, arg)),
        Statement::Return { meta, value } => {
            if value.contains_tuple(None) {
                Err(TupleError::boxed_report(&meta, "Tuple cannot be used in return values."))
            } else {
                Ok(build_return(meta, value))
            }
        }
        Statement::ConstraintEquality { meta, lhe, rhe } => {
            if lhe.contains_tuple(None) || rhe.contains_tuple(None) {
                Err(TupleError::boxed_report(
                    &meta,
                    "Tuples cannot be used together with the constraint equality operator `===`.",
                ))
            } else {
                Ok(build_constraint_equality(meta, lhe, rhe))
            }
        }
        Statement::Declaration { meta, xtype, name, dimensions, .. } => {
            for expr in &dimensions {
                if expr.contains_tuple(None) {
                    return Err(TupleError::boxed_report(
                        &meta,
                        "A tuple cannot be used to define the dimensions of an array.",
                    ));
                }
            }
            Ok(build_declaration(meta, xtype, name, dimensions))
        }
        Statement::InitializationBlock { meta, xtype, initializations } => {
            let mut new_inits = Vec::new();
            for stmt in initializations {
                let new_stmt = remove_tuples_from_statement(stmt)?;
                new_inits.push(new_stmt);
            }
            Ok(Statement::InitializationBlock { meta, xtype, initializations: new_inits })
        }
        Statement::Block { meta, stmts } => {
            let mut new_stmts = Vec::new();
            for stmt in stmts {
                let new_stmt = remove_tuples_from_statement(stmt)?;
                new_stmts.push(new_stmt);
            }
            Ok(Statement::Block { meta, stmts: new_stmts })
        }
        Statement::Substitution { meta, var, op, rhe, access } => {
            let new_rhe = remove_tuple_from_expression(rhe)?;
            if new_rhe.is_tuple() {
                return Err(TupleError::boxed_report(
                    &meta,
                    "Left-hand side of the statement is not a tuple.",
                ));
            }
            for access in &access {
                if let Access::ArrayAccess(index) = access {
                    if index.contains_tuple(None) {
                        return Err(TupleError::boxed_report(
                            index.meta(),
                            "A tuple cannot be used to access an array.",
                        ));
                    }
                }
            }
            if var != "_" {
                Ok(Statement::Substitution { meta, var, access, op, rhe: new_rhe })
            } else {
                // Since expressions cannot have side effects, we can ignore this.
                Ok(build_block(meta, Vec::new()))
            }
        }
    }
}

fn separate_tuple_for_log_call(values: Vec<Expression>) -> Vec<LogArgument> {
    let mut new_values = Vec::new();
    for value in values {
        if let Expression::Tuple { values: values2, .. } = value {
            new_values.push(LogArgument::LogStr("(".to_string()));
            let mut sep_values = separate_tuple_for_log_call(values2);
            new_values.append(&mut sep_values);
            new_values.push(LogArgument::LogStr(")".to_string()));
        } else {
            new_values.push(LogArgument::LogExp(value));
        }
    }
    new_values
}

fn remove_tuple_from_expression(expr: Expression) -> Result<Expression, Box<Report>> {
    use Expression::*;
    match expr.clone() {
        ArrayInLine { meta, values } => {
            for value in values {
                if value.contains_tuple(None) {
                    return Err(TupleError::boxed_report(
                        &meta,
                        "A tuple cannot be used to define the dimensions of an array.",
                    ));
                }
            }
            Ok(expr)
        }
        Number(_, _) => Ok(expr),
        Variable { meta, .. } => {
            if expr.contains_tuple(None) {
                return Err(TupleError::boxed_report(
                    &meta,
                    "A tuple cannot be used to access an array.",
                ));
            }
            Ok(expr)
        }
        InfixOp { meta, lhe, rhe, .. } => {
            if lhe.contains_tuple(None) || rhe.contains_tuple(None) {
                return Err(TupleError::boxed_report(
                    &meta,
                    "Tuples cannot be used in arithmetic or boolean expressions.",
                ));
            }
            Ok(expr)
        }
        PrefixOp { meta, rhe, .. } => {
            if rhe.contains_tuple(None) {
                return Err(TupleError::boxed_report(
                    &meta,
                    "Tuples cannot be used in arithmetic or boolean expressions.",
                ));
            }
            Ok(expr)
        }
        InlineSwitchOp { meta, cond, if_true, if_false } => {
            if cond.contains_tuple(None)
                || if_true.contains_tuple(None)
                || if_false.contains_tuple(None)
            {
                return Err(TupleError::boxed_report(
                    &meta,
                    "Tuples cannot be used inside an inline switch expression.",
                ));
            }
            Ok(expr)
        }
        Call { meta, args, .. } => {
            for value in args {
                if value.contains_tuple(None) {
                    return Err(TupleError::boxed_report(
                        &meta,
                        "Tuples cannot be used as an argument to a function call.",
                    ));
                }
            }
            Ok(expr)
        }
        AnonymousComponent { .. } => {
            // This is called after anonymous components have been removed.
            unreachable!();
        }
        Tuple { meta, values } => {
            let mut unfolded_values = Vec::new();
            for value in values {
                let new_value = remove_tuple_from_expression(value)?;
                if let Tuple { values: mut inner, .. } = new_value {
                    unfolded_values.append(&mut inner);
                } else {
                    unfolded_values.push(new_value);
                }
            }
            Ok(build_tuple(meta, unfolded_values))
        }
        ParallelOp { meta, rhe } => {
            if rhe.contains_tuple(None) {
                return Err(TupleError::boxed_report(
                    &meta,
                    "Tuples cannot be used in parallel operators.",
                ));
            }
            Ok(expr)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::parse_definition;

    use super::*;

    #[test]
    fn test_desugar_multi_sub() {
        let src = [
            r#"
            template Anonymous(n) {
                signal input a;
                signal input b;
                signal output c;
                signal output d;
                signal output e;

                (c, d, e) <== (a + 1, b + 2, c + 3);
            }
        "#,
            r#"
            template Test(n) {
                signal input a;
                signal input b;
                signal output c;
                signal output d;

                (c, _, d) <== Anonymous(n)(a, b);
            }
        "#,
        ];
        validate_ast(&src, 0);
    }

    #[test]
    fn test_nested_tuples() {
        let src = [r#"
            template Test(n) {
                signal input a;
                signal input b;
                signal output c;
                signal output d;
                signal output e;

                ((c, d), (_)) <== ((a + 1, b + 2), (c + 3));
            }
        "#];
        validate_ast(&src, 0);

        // TODO: Invalid, but is currently accepted by the compiler.
        let src = [r#"
            template Test(n) {
                signal input a;
                signal input b;
                signal output c;
                signal output d;
                signal output e;

                ((c, d), e) <== (a + 1, (b + 2, c + 3));
            }
        "#];
        validate_ast(&src, 0);

        // TODO: Invalid, but is currently accepted by the compiler.
        let src = [r#"
            template Test(n) {
                signal input a;
                signal input b;
                signal output c;

                (((c))) <== (a + b);
            }
        "#];
        validate_ast(&src, 0);
    }

    #[test]
    fn test_invalid_tuples() {
        let src = [r#"
            template Test(n) {
                signal input a;
                signal input b;
                signal output c;
                signal output d;
                signal output e;

                ((c, d), e) <== (b + 2, c + 3);
            }
        "#];
        validate_ast(&src, 1);
    }

    fn validate_ast(src: &[&str], errors: usize) {
        let mut reports = ReportCollection::new();
        let (templates, file_library) = parse_templates(src);

        // Verify that `remove_syntactic_sugar` is successful.
        let (templates, _) =
            remove_syntactic_sugar(&templates, &HashMap::new(), &file_library, &mut reports);
        assert_eq!(reports.len(), errors);

        // Ensure that no template contains a tuple or an anonymous component.
        for template in templates.values() {
            assert!(!template.get_body().contains_tuple(None));
            assert!(!template.get_body().contains_anonymous_component(None));
        }
    }

    fn parse_templates(src: &[&str]) -> (HashMap<String, TemplateData>, FileLibrary) {
        let mut templates = HashMap::new();
        let mut file_library = FileLibrary::new();
        let mut elem_id = 0;
        for src in src {
            let file_id = file_library.add_file("memory".to_string(), src.to_string(), true);
            let definition = parse_definition(src).unwrap();
            let Definition::Template {
                name,
                args,
                arg_location,
                body,
                parallel,
                is_custom_gate,
                ..
            } = definition
            else {
                unreachable!();
            };
            let template = TemplateData::new(
                name.clone(),
                file_id,
                body,
                args.len(),
                args,
                arg_location,
                &mut elem_id,
                parallel,
                is_custom_gate,
            );
            templates.insert(name, template);
        }
        (templates, file_library)
    }
}
