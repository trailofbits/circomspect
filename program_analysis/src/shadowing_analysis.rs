use anyhow::Result;
use log::{debug, info};

use super::errors::ShadowedVariableWarning;
use program_structure::ast::{Meta, Statement};
use program_structure::environment::VarEnvironment;
use program_structure::error_definition::{Report, ReportCollection};
use program_structure::program_archive::ProgramArchive;

pub fn shadowing_analysis(program: &ProgramArchive) -> Result<ReportCollection> {
    let mut reports = ReportCollection::new();
    for template in program.get_templates().values() {
        let mut env = build_environment(
            template.get_name_of_params(),
            template.get_body().get_meta(),
        );
        info!("visiting template '{}'", template.get_name());
        visit_statement(template.get_body(), &mut env, &mut reports);
    }
    for function in program.get_functions().values() {
        let mut env = build_environment(
            function.get_name_of_params(),
            function.get_body().get_meta(),
        );
        info!("visiting function '{}'", function.get_name());
        visit_statement(function.get_body(), &mut env, &mut reports);
    }
    Ok(reports)
}

fn build_environment(params: &Vec<String>, meta: &Meta) -> VarEnvironment<Meta> {
    params.iter().fold(VarEnvironment::new(), |mut env, param| {
        // We assume that parameter names are unique as this is enforced by the compiler.
        env.add_variable(param, meta.clone());
        env
    })
}

fn build_report(name: &str, primary_meta: &Meta, secondary_meta: &Meta) -> Report {
    ShadowedVariableWarning::produce_report(ShadowedVariableWarning {
        name: name.to_string(),
        primary_file_id: primary_meta.get_file_id(),
        primary_location: primary_meta.file_location(),
        secondary_file_id: secondary_meta.get_file_id(),
        secondary_location: secondary_meta.file_location(),
    })
}

fn visit_statement(
    stmt: &Statement,
    env: &mut VarEnvironment<Meta>,
    reports: &mut ReportCollection,
) {
    use Statement::*;
    match stmt {
        InitializationBlock {
            initializations, ..
        } => {
            for init in initializations {
                visit_statement(init, env, reports);
            }
        }
        Declaration { name, .. } => {
            debug!("visiting declaration of '{name}'");
            if let Some(meta) = env.get_variable(name) {
                reports.push(build_report(name, stmt.get_meta(), meta));
            }
            env.add_variable(name, stmt.get_meta().clone());
        }
        While { stmt, .. } => visit_statement(stmt, env, reports),
        Block { stmts, .. } => {
            debug!("visiting block statement");
            env.add_variable_block();
            for stmt in stmts {
                visit_statement(stmt, env, reports);
            }
            env.remove_variable_block();
        }
        IfThenElse {
            if_case, else_case, ..
        } => {
            visit_statement(if_case, env, reports);
            if let Some(else_case) = else_case {
                visit_statement(else_case, env, reports);
            }
        }
        _ => (),
    }
}
