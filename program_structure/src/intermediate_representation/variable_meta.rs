use std::collections::HashSet;

use super::ir::{AccessType, Meta, VariableName};

/// A variable use (a variable, component or signal read or write).
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct VariableUse {
    meta: Meta,
    name: VariableName,
    access: Vec<AccessType>,
}

impl VariableUse {
    pub fn new(meta: &Meta, name: &VariableName, access: &Vec<AccessType>) -> VariableUse {
        VariableUse {
            meta: meta.clone(),
            name: name.clone(),
            access: access.clone(),
        }
    }

    pub fn meta(&self) -> &Meta {
        &self.meta
    }

    pub fn name(&self) -> &VariableName {
        &self.name
    }

    pub fn access(&self) -> &Vec<AccessType> {
        &self.access
    }
}

pub type VariableUses = HashSet<VariableUse>;

pub trait VariableMeta {
    /// Compute variables read/written by the node. Must be called before either
    /// of the getters are called. To avoid interior mutability this needs to be
    /// called again whenever the node is mutated in a way that may invalidate
    /// the cached variable use.
    fn cache_variable_use(&mut self);

    /// Get the set of variables read by the IR node.
    #[must_use]
    fn locals_read(&self) -> &VariableUses;

    /// Get the set of variables written by the IR node.
    #[must_use]
    fn locals_written(&self) -> &VariableUses;

    /// Get the set of signals read by the IR node. Note that this does not
    /// include signals belonging to sub-components.
    #[must_use]
    fn signals_read(&self) -> &VariableUses;

    /// Get the set of signals written by the IR node. Note that this does not
    /// include signals belonging to sub-components.
    #[must_use]
    fn signals_written(&self) -> &VariableUses;

    /// Get the set of components read by the IR node. Note that a component
    /// read is typically a signal read for a signal exported by the component.
    #[must_use]
    fn components_read(&self) -> &VariableUses;

    /// Get the set of components written by the IR node. Note that a component
    /// write may either be a component initialization, or a signal write for a
    /// signal exported by the component.
    #[must_use]
    fn components_written(&self) -> &VariableUses;

    /// Get the set of variables read by the IR node. Note that this is simply
    /// the union of all locals, signals, and components read by the node.
    #[must_use]
    fn variables_read<'a>(&'a self) -> Box<dyn Iterator<Item = &'a VariableUse> + 'a> {
        let locals_read = self.locals_read().iter();
        let signals_read = self.signals_read().iter();
        let components_read = self.components_read().iter();
        Box::new(locals_read.chain(signals_read).chain(components_read))
    }

    /// Get the set of variables written by the IR node. Note that this is
    /// simply the union of all locals, signals, and components written.
    #[must_use]
    fn variables_written<'a>(&'a self) -> Box<dyn Iterator<Item = &'a VariableUse> + 'a> {
        let locals_written = self.locals_written().iter();
        let signals_written = self.signals_written().iter();
        let components_written = self.components_written().iter();
        Box::new(
            locals_written
                .chain(signals_written)
                .chain(components_written),
        )
    }

    /// Get the set of variables either read or written by the IR node.
    #[must_use]
    fn variables_used<'a>(&'a self) -> Box<dyn Iterator<Item = &'a VariableUse> + 'a> {
        Box::new(self.variables_read().chain(self.variables_written()))
    }
}

#[derive(Default, Clone)]
pub struct VariableKnowledge {
    variables_read: Option<VariableUses>,
    variables_written: Option<VariableUses>,
    signals_read: Option<VariableUses>,
    signals_written: Option<VariableUses>,
    components_read: Option<VariableUses>,
    components_written: Option<VariableUses>,
}

impl VariableKnowledge {
    #[must_use]
    pub fn new() -> VariableKnowledge {
        VariableKnowledge::default()
    }

    pub fn set_locals_read(&mut self, uses: &VariableUses) -> &mut VariableKnowledge {
        self.variables_read = Some(uses.clone());
        self
    }

    pub fn set_locals_written(&mut self, uses: &VariableUses) -> &mut VariableKnowledge {
        self.variables_written = Some(uses.clone());
        self
    }

    pub fn set_signals_read(&mut self, uses: &VariableUses) -> &mut VariableKnowledge {
        self.signals_read = Some(uses.clone());
        self
    }

    pub fn set_signals_written(&mut self, uses: &VariableUses) -> &mut VariableKnowledge {
        self.signals_written = Some(uses.clone());
        self
    }

    pub fn set_components_read(&mut self, uses: &VariableUses) -> &mut VariableKnowledge {
        self.components_read = Some(uses.clone());
        self
    }

    pub fn set_components_written(&mut self, uses: &VariableUses) -> &mut VariableKnowledge {
        self.components_written = Some(uses.clone());
        self
    }

    #[must_use]
    pub fn locals_read(&self) -> &VariableUses {
        self.variables_read
            .as_ref()
            .expect("variable knowledge must be initialized before it is read")
    }

    #[must_use]
    pub fn locals_written(&self) -> &VariableUses {
        self.variables_written
            .as_ref()
            .expect("variable knowledge must be initialized before it is read")
    }

    #[must_use]
    pub fn signals_read(&self) -> &VariableUses {
        self.signals_read
            .as_ref()
            .expect("variable knowledge must be initialized before it is read")
    }

    #[must_use]
    pub fn signals_written(&self) -> &VariableUses {
        self.signals_written
            .as_ref()
            .expect("variable knowledge must be initialized before it is read")
    }

    #[must_use]
    pub fn components_read(&self) -> &VariableUses {
        self.components_read
            .as_ref()
            .expect("variable knowledge must be initialized before it is read")
    }

    #[must_use]
    pub fn components_written(&self) -> &VariableUses {
        self.components_written
            .as_ref()
            .expect("variable knowledge must be initialized before it is read")
    }

    #[must_use]
    pub fn variables_read<'a>(&'a self) -> Box<dyn Iterator<Item = &'a VariableUse> + 'a> {
        let locals_read = self.locals_read().iter();
        let signals_read = self.signals_read().iter();
        let components_read = self.components_read().iter();
        Box::new(locals_read.chain(signals_read).chain(components_read))
    }

    #[must_use]
    pub fn variables_written<'a>(&'a self) -> Box<dyn Iterator<Item = &'a VariableUse> + 'a> {
        let locals_written = self.locals_written().iter();
        let signals_written = self.signals_written().iter();
        let components_written = self.components_written().iter();
        Box::new(
            locals_written
                .chain(signals_written)
                .chain(components_written),
        )
    }
}
