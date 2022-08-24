use std::fmt;
use std::collections::HashMap;
use num_bigint::BigInt;

use super::ir::VariableName;

#[derive(Default, Clone)]
pub struct ValueEnvironment {
    reduces_to: HashMap<VariableName, ValueReduction>
}

impl ValueEnvironment {
    pub fn new() -> ValueEnvironment {
        ValueEnvironment::default()
    }

    /// Set the value of the given variable. Returns `true` on first update.
    ///
    /// Panics
    ///
    /// This function panics if the caller attempts to set two different values
    /// for the same variable.
    pub fn add_variable(&mut self, name: &VariableName, value: &ValueReduction) -> bool {
        if let Some(previous) = self.reduces_to.insert(name.clone(), value.clone()) {
            assert_eq!(previous, *value);
            false
        } else {
            true
        }
    }

    pub fn get_variable(&self, name: &VariableName) -> Option<&ValueReduction> {
        self.reduces_to.get(name)
    }
}

pub trait ValueMeta {
    /// Propagate variable values defined by the environment to each sub-node.
    /// The method returns true if the node (or a sub-node) was updated.
    fn propagate_values(&mut self, env: &mut ValueEnvironment) -> bool;

    /// Returns true if the node reduces to a constant value.
    #[must_use]
    fn is_constant(&self) -> bool;

    /// Returns true if the node reduces to a boolean value.
    #[must_use]
    fn is_boolean(&self) -> bool;

    /// Returns true if the node reduces to a field element.
    #[must_use]
    fn is_field_element(&self) -> bool;

    /// Returns the value if the node reduces to a constant, and None otherwise.
    #[must_use]
    fn value(&self) -> Option<&ValueReduction>;
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum ValueReduction {
    Boolean { value: bool },
    FieldElement { value: BigInt },
}

impl fmt::Display for ValueReduction {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use ValueReduction::*;
        match self {
            Boolean { value } => write!(f, "{value}"),
            FieldElement { value } => write!(f, "{value}"),
        }
    }
}

#[derive(Default, Clone)]
pub struct ValueKnowledge {
    reduces_to: Option<ValueReduction>,
}

impl ValueKnowledge {
    #[must_use]
    pub fn new() -> ValueKnowledge {
        ValueKnowledge::default()
    }

    /// Sets the value of the node. Returns `true` on the first update.
    #[must_use]
    pub fn set_reduces_to(&mut self, reduces_to: ValueReduction) -> bool {
        let result = self.reduces_to.is_none();
        self.reduces_to = Some(reduces_to);
        result
    }

    /// Gets the value of the node. Returns `None` if the value is unknown.
    #[must_use]
    pub fn get_reduces_to(&self) -> Option<&ValueReduction> {
        self.reduces_to.as_ref()
    }

    /// Returns `true` if the value of the node is known.
    #[must_use]
    pub fn is_constant(&self) -> bool {
        self.reduces_to.is_some()
    }

    /// Returns `true` if the value of the node is a boolean.
    #[must_use]
    pub fn is_boolean(&self) -> bool {
        use ValueReduction::*;
        matches!(self.reduces_to, Some(Boolean { .. }))
    }

    /// Returns `true` if the value of the node is a field element.
    #[must_use]
    pub fn is_field_element(&self) -> bool {
        use ValueReduction::*;
        matches!(self.reduces_to, Some(FieldElement { .. }))
    }
}
