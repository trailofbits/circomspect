use crate::ast::Definition;
use crate::file_definition::{FileID, FileLocation};
use crate::function_data::FunctionData;
use crate::template_data::TemplateData;

use crate::ir::VariableName;

pub struct Parameters {
    param_names: Vec<VariableName>,
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl Parameters {
    #[must_use]
    pub fn new(
        param_names: &[String],
        file_id: Option<FileID>,
        file_location: FileLocation,
    ) -> Parameters {
        Parameters {
            param_names: param_names.iter().map(VariableName::from_name).collect(),
            file_id,
            file_location,
        }
    }

    #[must_use]
    pub fn file_id(&self) -> &Option<FileID> {
        &self.file_id
    }

    #[must_use]
    pub fn file_location(&self) -> &FileLocation {
        &self.file_location
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.param_names.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn iter(&self) -> impl Iterator<Item = &VariableName> {
        self.param_names.iter()
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut VariableName> {
        self.param_names.iter_mut()
    }

    pub fn contains(&self, param_name: &VariableName) -> bool {
        self.param_names.contains(param_name)
    }
}

impl From<&FunctionData> for Parameters {
    fn from(function: &FunctionData) -> Parameters {
        Parameters::new(
            function.get_name_of_params(),
            Some(function.get_file_id()),
            function.get_param_location(),
        )
    }
}

impl From<&TemplateData> for Parameters {
    fn from(template: &TemplateData) -> Parameters {
        Parameters::new(
            template.get_name_of_params(),
            Some(template.get_file_id()),
            template.get_param_location(),
        )
    }
}

impl From<&Definition> for Parameters {
    fn from(definition: &Definition) -> Parameters {
        match definition {
            Definition::Function { meta, args, arg_location, .. }
            | Definition::Template { meta, args, arg_location, .. } => {
                Parameters::new(args, meta.file_id, arg_location.clone())
            }
        }
    }
}
