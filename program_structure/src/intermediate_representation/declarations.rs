use std::collections::HashMap;

use crate::file_definition::{FileID, FileLocation};
use crate::ir::*;

/// A structure used to track declared variables.
#[derive(Default, Clone)]
pub struct Declarations(HashMap<VariableName, Declaration>);

impl Declarations {
    #[must_use]
    pub fn new() -> Declarations {
        Declarations::default()
    }

    pub fn add_declaration(&mut self, declaration: &Declaration) {
        assert!(
            self.0
                .insert(declaration.variable_name().clone(), declaration.clone())
                .is_none(),
            "variable `{}` already tracked by declaration map",
            declaration.variable_name()
        );
    }

    #[must_use]
    pub fn get_declaration(&self, name: &VariableName) -> Option<&Declaration> {
        self.0.get(&name.without_version())
    }

    #[must_use]
    pub fn get_type(&self, name: &VariableName) -> Option<&VariableType> {
        self.get_declaration(name).map(|decl| decl.variable_type())
    }

    pub fn iter(&self) -> impl Iterator<Item = (&VariableName, &Declaration)> {
        self.0.iter()
    }

    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// To avoid having to add a new declaration for each new version of a variable
/// we track all declarations as part of the CFG header.
#[derive(Clone)]
pub struct Declaration {
    name: VariableName,
    var_type: VariableType,
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl Declaration {
    pub fn new(
        name: &VariableName,
        var_type: &VariableType,
        file_id: &Option<FileID>,
        file_location: &FileLocation,
    ) -> Declaration {
        Declaration {
            name: name.clone(),
            var_type: var_type.clone(),
            file_id: file_id.clone(),
            file_location: file_location.clone(),
        }
    }

    #[must_use]
    pub fn file_id(&self) -> Option<FileID> {
        self.file_id
    }

    #[must_use]
    pub fn file_location(&self) -> FileLocation {
        self.file_location.clone()
    }

    #[must_use]
    pub fn variable_name(&self) -> &VariableName {
        &self.name
    }

    #[must_use]
    pub fn variable_type(&self) -> &VariableType {
        &&self.var_type
    }
}
