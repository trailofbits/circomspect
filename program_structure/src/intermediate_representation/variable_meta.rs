use std::collections::HashSet;

use super::ir::VariableName;

pub type VariableSet = HashSet<VariableName>;

pub trait VariableMeta {
    /// Compute variables read/written by the node. Must be called before either
    /// of the getters are called. To avoid interior mutability this needs to be
    /// called again whenever the node is mutated in a way that may invalidate
    /// the cached variable use.
    fn cache_variable_use(&mut self);

    /// Get the names of all variables read by the IR node.
    #[must_use]
    fn get_variables_read(&self) -> &VariableSet;

    /// Get the names of all variables written by the IR node.
    #[must_use]
    fn get_variables_written(&self) -> &VariableSet;

    /// Get the names of all signals read by the IR node.
    #[must_use]
    fn get_signals_read(&self) -> &VariableSet;

    /// Get the names of all signals written by the IR node.
    #[must_use]
    fn get_signals_written(&self) -> &VariableSet;
}

#[derive(Default, Clone)]
pub struct VariableKnowledge {
    variables_read: Option<VariableSet>,
    variables_written: Option<VariableSet>,
    signals_read: Option<VariableSet>,
    signals_written: Option<VariableSet>,
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

    pub fn set_variables_read(&mut self, names: &VariableSet) -> &mut Self {
        self.variables_read = Some(names.clone());
        self
    }

    pub fn set_variables_written(&mut self, names: &VariableSet) -> &mut Self {
        self.variables_written = Some(names.clone());
        self
    }

    pub fn set_signals_read(&mut self, names: &VariableSet) -> &mut Self {
        self.signals_read = Some(names.clone());
        self
    }

    pub fn set_signals_written(&mut self, names: &VariableSet) -> &mut Self {
        self.signals_written = Some(names.clone());
        self
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

    #[must_use]
    pub fn get_signals_read(&self) -> &VariableSet {
        self.signals_read
            .as_ref()
            .expect("variable knowledge must be initialized before it is read")
    }

    #[must_use]
    pub fn get_signals_written(&self) -> &VariableSet {
        self.signals_written
            .as_ref()
            .expect("variable knowledge must be initialized before it is read")
    }
}
