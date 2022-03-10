use log::debug;
use anyhow::{anyhow, Result};
use std::collections::HashMap;

use super::visitor::Visitor;
use super::errors::ShadowedVariableWarning;
use program_structure::program_archive::ProgramArchive;
use program_structure::error_definition::ReportCollection;
use program_structure::ast::{Expression, Meta, VariableType, Statement};

#[derive(Default, Clone)]
struct Scope {
    parent: Option<Box<Scope>>,
    variables: HashMap<String, Meta>,
}

impl Scope {
    fn push(&self) -> Scope {
        Scope {
            parent: Some(Box::new(self.clone())),
            variables: self.variables.clone()
        }
    }

    fn pop(&self) -> Result<Scope> {
        if let Some(parent) = &self.parent {
            Ok(*parent.clone())
        } else {
            Err(anyhow!("cannot pop outermost scope"))
        }
    }

    fn add(&mut self, var: &str, meta: &Meta) -> Option<&Meta> {
        if self.variables.contains_key(var) {
            self.variables.get(var)
        } else {
            self.variables.insert(var.to_string(), meta.clone());
            None
        }
    }
}

#[derive(Default)]
pub struct ShadowingAnalysis {
    scope: Scope,
    reports: ReportCollection
}

impl ShadowingAnalysis {
    pub fn new() -> ShadowingAnalysis {
        ShadowingAnalysis::default()
    }

    pub fn run(&mut self, program: &ProgramArchive) -> ReportCollection {
        self.visit_templates(&program.templates);
        self.visit_functions(&program.functions);
        self.reports.clone()
    }
}

impl Visitor for ShadowingAnalysis {
    fn visit_block(&mut self, _meta: &Meta, stmts: &[Statement]) {
        self.scope = self.scope.push();
        for stmt in stmts {
            self.visit_stmt(stmt);
        }
        self.scope
            .pop()
            .expect("not in outermost scope");
    }

    fn visit_expr(&mut self, _: &Expression) {
        // Override visit_expr to ignore expressions.
    }

    fn visit_declaration(&mut self, primary_meta: &Meta, _xtype: &VariableType, name: &str, _dimensions: &[Expression], _is_constant: &bool) {
        if let Some(secondary_meta) = self.scope.add(name, primary_meta) {
            debug!("declaration of {name} shadows previous declaration");
            self.reports.push(ShadowedVariableWarning::produce_report(ShadowedVariableWarning {
                name: name.to_string(),
                primary_file_id: primary_meta.get_file_id(),
                primary_location: primary_meta.file_location(),
                secondary_file_id: secondary_meta.get_file_id(),
                secondary_location: secondary_meta.file_location(),
            }));
        }
    }
}
