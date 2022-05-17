use crate::file_definition::{FileID, FileLocation};
use crate::function_data::FunctionData;
use crate::template_data::TemplateData;

use super::ir::{IREnvironment, VariableName};

pub struct ParameterData {
    param_names: Vec<VariableName>,
    file_id: FileID,
    file_location: FileLocation,
}

impl ParameterData {
    pub fn new(
        param_names: &Vec<String>,
        file_id: FileID,
        file_location: FileLocation,
    ) -> ParameterData {
        ParameterData {
            param_names: param_names.iter().map(VariableName::name).collect(),
            file_id,
            file_location,
        }
    }
    pub fn get_name(&self, i: usize) -> &VariableName {
        &self.param_names[i]
    }
    pub fn get_file_id(&self) -> FileID {
        self.file_id
    }
    pub fn get_location(&self) -> FileLocation {
        self.file_location.clone()
    }
    pub fn len(&self) -> usize {
        self.param_names.len()
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
            function.get_file_id(),
            function.get_param_location().clone(),
        )
    }
}

impl From<&TemplateData> for ParameterData {
    fn from(template: &TemplateData) -> ParameterData {
        ParameterData::new(
            template.get_name_of_params(),
            template.get_file_id(),
            template.get_param_location().clone(),
        )
    }
}

impl From<&ParameterData> for IREnvironment {
    fn from(param_data: &ParameterData) -> IREnvironment {
        let mut env = IREnvironment::new();
        for name in param_data.iter() {
            env.add_variable(&name.to_string(), ());
        }
        env
    }
}
