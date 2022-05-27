use crate::ast::Definition;
use crate::file_definition::{FileID, FileLocation};
use crate::function_data::FunctionData;
use crate::ir::declaration_map::{Declaration, VariableType};
use crate::template_data::TemplateData;

use crate::ir::{IREnvironment, VariableName};

pub struct ParameterData {
    param_names: Vec<VariableName>,
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl ParameterData {
    #[must_use]
    pub fn new(
        param_names: &[String],
        file_id: Option<FileID>,
        file_location: FileLocation,
    ) -> ParameterData {
        ParameterData {
            param_names: param_names.iter().map(VariableName::name).collect(),
            file_id,
            file_location,
        }
    }

    #[must_use]
    pub fn get_name(&self, i: usize) -> &VariableName {
        &self.param_names[i]
    }

    #[must_use]
    pub fn get_file_id(&self) -> &Option<FileID> {
        &self.file_id
    }

    #[must_use]
    pub fn get_location(&self) -> FileLocation {
        self.file_location.clone()
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.param_names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> impl Iterator<Item = &VariableName> {
        self.param_names.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut VariableName> {
        self.param_names.iter_mut()
    }
}

impl From<&FunctionData> for ParameterData {
    fn from(function: &FunctionData) -> ParameterData {
        ParameterData::new(
            function.get_name_of_params(),
            Some(function.get_file_id()),
            function.get_param_location(),
        )
    }
}

impl From<&TemplateData> for ParameterData {
    fn from(template: &TemplateData) -> ParameterData {
        ParameterData::new(
            template.get_name_of_params(),
            Some(template.get_file_id()),
            template.get_param_location(),
        )
    }
}

impl From<&Definition> for ParameterData {
    fn from(definition: &Definition) -> ParameterData {
        match definition {
            Definition::Function {
                meta,
                args,
                arg_location,
                ..
            }
            | Definition::Template {
                meta,
                args,
                arg_location,
                ..
            } => ParameterData::new(args, meta.file_id, arg_location.clone()),
        }
    }
}

impl From<&ParameterData> for IREnvironment {
    fn from(param_data: &ParameterData) -> IREnvironment {
        let mut env = IREnvironment::new();
        for name in param_data.iter() {
            let declaration = Declaration::new(
                name,
                &VariableType::Var,
                &Vec::new(),
                param_data.file_id,
                &param_data.file_location,
            );
            env.add_declaration(&name.to_string(), declaration);
        }
        env
    }
}
