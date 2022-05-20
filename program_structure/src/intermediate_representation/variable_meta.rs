use std::collections::HashSet;

use super::ir::VariableName;

pub type VariableSet = HashSet<VariableName>;

pub trait VariableMeta {
    /// Compute variables read/written by the node. Must be called before either
    /// of the getters are called. To avoid interior mutability this needs to be
    /// called again whenever the node is mutated in a way that may invalidate
    /// the cached variable use.
    fn cache_variable_use(&mut self);

    /// Get the names of all variables read by the node.
    #[must_use]
    fn get_variables_read(&self) -> &VariableSet;

    /// Get the names of all variables written by the node.
    #[must_use]
    fn get_variables_written(&self) -> &VariableSet;
}

#[derive(Default, Clone)]
pub struct VariableKnowledge {
    variables_read: Option<VariableSet>,
    variables_written: Option<VariableSet>,
}

impl VariableKnowledge {
    #[must_use]
    pub fn new() -> VariableKnowledge {
        VariableKnowledge::default()
    }

    #[must_use]
    pub fn is_cached(&self) -> bool {
        matches!(self.variables_read, Some(_)) && matches!(self.variables_written, Some(_))
    }

    pub fn add_variable_read(&mut self, name: &VariableName) {
        if let Some(variables_read) = self.variables_read.as_mut() {
            variables_read.insert(name.clone());
        } else {
            self.variables_read = Some(VariableSet::from([name.clone()]))
        }
    }

    pub fn set_variables_read(&mut self, names: &VariableSet) {
        self.variables_read = Some(names.clone())
    }

    pub fn add_variable_written(&mut self, name: &VariableName) {
        if let Some(variables_written) = self.variables_read.as_mut() {
            variables_written.insert(name.clone());
        } else {
            self.variables_written = Some(VariableSet::from([name.clone()]))
        }
    }

    pub fn set_variables_written(&mut self, names: &VariableSet) {
        self.variables_written = Some(names.clone())
    }

    #[must_use]
    pub fn get_variables_read(&self) -> &VariableSet {
        self.variables_read
            .as_ref()
            .expect("variable knowledge must be initialized before it is read")
    }

    #[must_use]
    pub fn get_variables_written(&self) -> &VariableSet {
        self.variables_written
            .as_ref()
            .expect("variable knowledge must be initialized before it is read")
    }
}
