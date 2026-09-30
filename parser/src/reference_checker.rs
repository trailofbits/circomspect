use program_structure::ast::Expression;
use program_structure::file_definition::FileID;
use program_structure::function_data::FunctionInfo;
use program_structure::report::{Report, ReportCollection};
use program_structure::report_code::ReportCode;
use program_structure::template_data::TemplateInfo;

use crate::syntax_sugar_traits::ContainsExpression;

/// Reports unresolved calls and main calls that resolve to functions.
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
    if let Some(main) = main {
        main.visit_expressions(&mut collect_unresolved);
        if let Some(report) = wrong_main_target(main, templates, functions) {
            unresolved.push(report);
        }
    }
    unresolved.sort_by_key(|(file_id, start, _)| (*file_id, *start));
    reports.extend(unresolved.into_iter().map(|(_, _, report)| report));
}

fn wrong_main_target(
    main: &Expression,
    templates: &TemplateInfo,
    functions: &FunctionInfo,
) -> Option<(FileID, usize, Report)> {
    let call = if let Expression::ParallelOp { rhe, .. } = main { rhe.as_ref() } else { main };
    let Expression::Call { meta, id, .. } = call else {
        return None;
    };
    if templates.contains_key(id) || !functions.contains_key(id) {
        return None;
    }

    let mut report = Report::error(
        format!("The main component target `{id}` is a function; a template is required."),
        ReportCode::UndefinedTemplate,
    );
    report.add_primary(
        meta.file_location(),
        meta.get_file_id(),
        "Function called here.".to_string(),
    );
    Some((meta.get_file_id(), meta.get_start(), report))
}
