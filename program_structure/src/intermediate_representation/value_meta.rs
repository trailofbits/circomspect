use num_bigint::BigInt;

use crate::environment::VarEnvironment;

pub type ValueEnvironment = VarEnvironment<ValueReduction>;

pub trait ValueMeta {
    /// Propagate variable values defined by the environment to each sub-node.
    /// The method returns true if the node (or a sub-node) was updated.
    fn propagate_values(&mut self, env: &mut VarEnvironment<ValueReduction>) -> bool;

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
    fn get_reduces_to(&self) -> Option<&ValueReduction>;
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum ValueReduction {
    Boolean { value: bool },
    FieldElement { value: BigInt },
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

    pub fn set_reduces_to(&mut self, reduces_to: ValueReduction) -> bool {
        let result = self.reduces_to.is_none();
        self.reduces_to = Option::Some(reduces_to);
        result
    }

    #[must_use]
    pub fn get_reduces_to(&self) -> Option<&ValueReduction> {
        self.reduces_to.as_ref()
    }

    #[must_use]
    pub fn is_constant(&self) -> bool {
        self.reduces_to.is_some()
    }

    #[must_use]
    pub fn is_boolean(&self) -> bool {
        use ValueReduction::*;
        matches!(self.reduces_to, Some(Boolean { .. }))
    }

    #[must_use]
    pub fn is_field_element(&self) -> bool {
        use ValueReduction::*;
        matches!(self.reduces_to, Some(FieldElement { .. }))
    }
}
