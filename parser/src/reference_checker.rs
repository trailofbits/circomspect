use program_structure::ast::{Expression, Statement, VariableType};
use program_structure::file_definition::FileID;
use program_structure::function_data::FunctionInfo;
use program_structure::report::{Report, ReportCollection};
use program_structure::report_code::ReportCode;
use program_structure::template_data::TemplateInfo;

use crate::syntax_sugar_traits::{ContainsExpression, ContainsStatement};

#[derive(Clone, Copy)]
enum TemplateCallContext {
    Main,
    ComponentInitializer,
}

impl TemplateCallContext {
    fn description(self) -> &'static str {
        match self {
            Self::Main => "main component",
            Self::ComponentInitializer => "component initializer",
        }
    }
}

/// Reports unresolved calls and component calls that resolve to functions.
pub(crate) fn report_unresolved_calls(
    templates: &TemplateInfo,
    functions: &FunctionInfo,
    main: Option<&Expression>,
    reports: &mut ReportCollection,
) {
    let mut unresolved = Vec::new();
    let mut collect_unresolved = |expression: &Expression| {
        let Expression::Call { meta, id, .. } = expression else {
            return;
        };
        if templates.contains_key(id) || functions.contains_key(id) {
            return;
        }

        let mut report = Report::error(
            format!("The call target `{id}` is not defined as a function or template."),
            ReportCode::UnresolvedCall,
        );
        report.add_primary(
            meta.file_location(),
            meta.get_file_id(),
            format!("Unresolved call to `{id}`."),
        );
        unresolved.push((meta.get_file_id(), meta.get_start(), report));
    };
    for body in templates
        .values()
        .map(|template| template.get_body())
        .chain(functions.values().map(|function| function.get_body()))
    {
        body.visit_expressions(&mut collect_unresolved);
    }
    let mut wrong_kind = Vec::new();
    for template in templates.values() {
        template.get_body().visit_statements(&mut |statement| {
            let Statement::InitializationBlock {
                xtype: VariableType::Component,
                initializations,
                ..
            } = statement
            else {
                return;
            };
            for initialization in initializations {
                let Statement::Substitution { rhe, .. } = initialization else {
                    continue;
                };
                if let Some(report) = wrong_template_target(
                    rhe,
                    templates,
                    functions,
                    TemplateCallContext::ComponentInitializer,
                ) {
                    wrong_kind.push(report);
                }
            }
        });
    }
    if let Some(main) = main {
        main.visit_expressions(&mut collect_unresolved);
        if let Some(report) =
            wrong_template_target(main, templates, functions, TemplateCallContext::Main)
        {
            wrong_kind.push(report);
        }
    }
    unresolved.extend(wrong_kind);
    unresolved.sort_by_key(|(file_id, start, _)| (*file_id, *start));
    reports.extend(unresolved.into_iter().map(|(_, _, report)| report));
}

fn wrong_template_target(
    expression: &Expression,
    templates: &TemplateInfo,
    functions: &FunctionInfo,
    context: TemplateCallContext,
) -> Option<(FileID, usize, Report)> {
    let call =
        if let Expression::ParallelOp { rhe, .. } = expression { rhe.as_ref() } else { expression };
    let Expression::Call { meta, id, .. } = call else {
        return None;
    };
    if templates.contains_key(id) || !functions.contains_key(id) {
        return None;
    }

    let mut report = Report::error(
        format!(
            "The {} target `{id}` is a function; a template is required.",
            context.description()
        ),
        ReportCode::UndefinedTemplate,
    );
    report.add_primary(
        meta.file_location(),
        meta.get_file_id(),
        "Function called here.".to_string(),
    );
    Some((meta.get_file_id(), meta.get_start(), report))
}
