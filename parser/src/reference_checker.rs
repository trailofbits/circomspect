use std::collections::HashMap;

use program_structure::ast::{Access, AssignOp, Expression, Statement, VariableType};
use program_structure::file_definition::FileID;
use program_structure::function_data::FunctionInfo;
use program_structure::report::{Report, ReportCollection};
use program_structure::report_code::ReportCode;
use program_structure::template_data::TemplateInfo;
use program_structure::nonempty_vec::NonEmptyVec;

use crate::syntax_sugar_traits::{ContainsExpression, ContainsStatement, StatementVisitor};

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
        let mut component_visitor = ComponentTargetVisitor {
            templates,
            functions,
            scopes: NonEmptyVec::new(HashMap::new()),
            reports: Vec::new(),
        };
        template.get_body().visit_statements(&mut component_visitor);
        wrong_kind.extend(component_visitor.reports);
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

struct ComponentTargetVisitor<'a> {
    templates: &'a TemplateInfo,
    functions: &'a FunctionInfo,
    scopes: NonEmptyVec<HashMap<String, VariableType>>,
    reports: Vec<(FileID, usize, Report)>,
}

impl ComponentTargetVisitor<'_> {
    fn visible_type(&self, name: &str) -> Option<&VariableType> {
        for index in (0..self.scopes.len()).rev() {
            if let Some(xtype) = self.scopes[index].get(name) {
                return Some(xtype);
            }
        }
        None
    }

    fn visit_assignment(&mut self, var: &str, access: &[Access], rhe: &Expression) {
        let Some(VariableType::Component) = self.visible_type(var) else {
            return;
        };
        for item in access {
            match item {
                Access::ArrayAccess(_) => {}
                Access::ComponentAccess(_) => return,
            }
        }
        if let Some(report) = wrong_template_target(
            rhe,
            self.templates,
            self.functions,
            TemplateCallContext::ComponentInitializer,
        ) {
            self.reports.push(report);
        }
    }
}

impl StatementVisitor for ComponentTargetVisitor<'_> {
    fn visit(&mut self, statement: &Statement) {
        match statement {
            Statement::Declaration { xtype, name, .. } => {
                self.scopes.last_mut().insert(name.clone(), xtype.clone());
            }
            Statement::Substitution { var, access, op: AssignOp::AssignVar, rhe, .. } => {
                self.visit_assignment(var, access, rhe);
            }
            Statement::IfThenElse { .. }
            | Statement::While { .. }
            | Statement::Return { .. }
            | Statement::InitializationBlock { .. }
            | Statement::Substitution { .. }
            | Statement::MultiSubstitution { .. }
            | Statement::ConstraintEquality { .. }
            | Statement::LogCall { .. }
            | Statement::Block { .. }
            | Statement::Assert { .. } => {}
        }
    }

    fn enter_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn leave_scope(&mut self) {
        let _ = self.scopes.pop();
    }
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
