use std::collections::HashSet;

pub type VariableSet = HashSet<String>;

pub trait VariableMeta {
    /// Compute variables read/written by the node. Must be called before either
    /// of the getters are called. To avoid interior mutability this needs to be
    /// called again whenever the node is mutated in a way that may invalidate
    /// the cached variable use.
    fn cache_variable_use(&mut self);

    /// Get the names of all variables read by the node.
    fn get_variables_read(&self) -> &VariableSet;

    /// Get the names of all variables written by the node.
    fn get_variables_written(&self) -> &VariableSet;
}

#[derive(Default, Clone)]
pub struct VariableKnowledge {
    variables_read: Option<HashSet<String>>,
    variables_written: Option<HashSet<String>>,
}

impl VariableKnowledge {
    pub fn new() -> VariableKnowledge {
        VariableKnowledge::default()
    }

    pub fn is_cached(&self) -> bool {
        matches!(self.variables_read, Some(_)) && matches!(self.variables_written, Some(_))
    }

    pub fn add_variable_read(&mut self, name: &str) {
        if let Some(variables_read) = self.variables_read.as_mut() {
            variables_read.insert(name.to_string());
        } else {
            self.variables_read = Some(HashSet::from([name.to_string()]))
        }
    }

    pub fn set_variables_read(&mut self, names: &HashSet<String>) {
        self.variables_read = Some(names.clone())
    }

    pub fn add_variable_written(&mut self, name: &str) {
        if let Some(variables_written) = self.variables_read.as_mut() {
            variables_written.insert(name.to_string());
        } else {
            self.variables_written = Some(HashSet::from([name.to_string()]))
        }
    }

    pub fn set_variables_written(&mut self, names: &HashSet<String>) {
        self.variables_written = Some(names.clone())
    }

    pub fn get_variables_read(&self) -> &VariableSet {
        self.variables_read
            .as_ref()
            .expect("variable knowledge must be initialized before it is read")
    }

    pub fn get_variables_written(&self) -> &VariableSet {
        self.variables_written
            .as_ref()
            .expect("variable knowledge must be initialized before it is read")
    }
}
