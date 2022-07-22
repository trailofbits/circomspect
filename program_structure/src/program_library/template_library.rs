use std::collections::HashMap;

use crate::ast::Definition;
use crate::file_definition::{FileID, FileLibrary};
use crate::function_data::{FunctionData, FunctionInfo};
use crate::template_data::{TemplateData, TemplateInfo};

type Contents = HashMap<FileID, Vec<Definition>>;

pub struct TemplateLibrary {
    pub functions: FunctionInfo,
    pub templates: TemplateInfo,
    pub file_library: FileLibrary,
}

impl TemplateLibrary {
    pub fn new(library_contents: Contents, file_library: FileLibrary) -> TemplateLibrary {
        let mut functions = HashMap::new();
        let mut templates = HashMap::new();

        let mut elem_id = 0;
        for (file_id, file_contents) in library_contents {
            for definition in file_contents {
                match definition {
                    Definition::Function {
                        name,
                        args,
                        arg_location,
                        body,
                        ..
                    } => {
                        functions.insert(
                            name.clone(),
                            FunctionData::new(
                                name,
                                file_id,
                                body,
                                args.len(),
                                args,
                                arg_location,
                                &mut elem_id,
                            ),
                        );
                    }
                    Definition::Template {
                        name,
                        args,
                        arg_location,
                        body,
                        parallel,
                        ..
                    } => {
                        templates.insert(
                            name.clone(),
                            TemplateData::new(
                                name,
                                file_id,
                                body,
                                args.len(),
                                args,
                                arg_location,
                                &mut elem_id,
                                parallel,
                            ),
                        );
                    }
                }
            }
        }
        TemplateLibrary {
            functions,
            templates,
            file_library,
        }
    }
    // Template methods.
    pub fn contains_template(&self, template_name: &str) -> bool {
        self.templates.contains_key(template_name)
    }

    pub fn get_template(&self, template_name: &str) -> &TemplateData {
        assert!(self.contains_template(template_name));
        self.templates.get(template_name).unwrap()
    }

    pub fn get_template_mut(&mut self, template_name: &str) -> &mut TemplateData {
        assert!(self.contains_template(template_name));
        self.templates.get_mut(template_name).unwrap()
    }

    pub fn get_templates(&self) -> &TemplateInfo {
        &self.templates
    }

    pub fn get_templates_mut(&mut self) -> &mut TemplateInfo {
        &mut self.templates
    }

    // Function methods.
    pub fn contains_function(&self, function_name: &str) -> bool {
        self.functions.contains_key(function_name)
    }

    pub fn get_function(&self, function_name: &str) -> &FunctionData {
        assert!(self.contains_function(function_name));
        self.functions.get(function_name).unwrap()
    }

    pub fn get_function_mut(&mut self, function_name: &str) -> &mut FunctionData {
        assert!(self.contains_function(function_name));
        self.functions.get_mut(function_name).unwrap()
    }

    pub fn get_functions(&self) -> &FunctionInfo {
        &self.functions
    }

    pub fn get_functions_mut(&mut self) -> &mut FunctionInfo {
        &mut self.functions
    }

    pub fn get_file_library(&self) -> &FileLibrary {
        &self.file_library
    }
}
