use num_bigint::{BigInt, Sign};
use num_traits::Zero;
use std::collections::HashMap;
use std::fmt;

use crate::constants::UsefulConstants;

use super::ir::VariableName;

#[derive(Clone)]
pub struct ValueEnvironment {
    constants: UsefulConstants,
    reduces_to: HashMap<VariableName, ValueReduction>,
}

impl ValueEnvironment {
    pub fn new(constants: &UsefulConstants) -> ValueEnvironment {
        ValueEnvironment { constants: constants.clone(), reduces_to: HashMap::new() }
    }

    /// Set the value of the given variable. Returns `true` on updates.
    pub fn add_variable(&mut self, name: &VariableName, value: &ValueReduction) -> bool {
        let prev_value = self.reduces_to.get(name).cloned().unwrap_or_default();
        let new_value = prev_value.intersect(value);
        if new_value != prev_value {
            self.reduces_to.insert(name.clone(), new_value);
            true
        } else {
            false
        }
    }

    #[must_use]
    pub fn get_variable(&self, name: &VariableName) -> ValueReduction {
        self.reduces_to.get(name).cloned().unwrap_or_default()
    }

    /// Returns the prime used.
    pub fn prime(&self) -> &BigInt {
        self.constants.prime()
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
    fn value(&self) -> ValueReduction;
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum ValueReduction {
    Unknown,
    Boolean(Option<bool>),
    FieldElement(Option<BigInt>),
    Impossible,
}

impl Default for ValueReduction {
    fn default() -> Self {
        Self::Unknown
    }
}

impl fmt::Display for ValueReduction {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use ValueReduction::*;
        match self {
            Boolean(Some(value)) => write!(f, "{value}"),
            Boolean(None) => write!(f, "<bool>"),
            FieldElement(Some(value)) => write!(f, "{value}"),
            FieldElement(None) => write!(f, "<felt>"),
            Unknown => write!(f, "<unknown>"),
            Impossible => write!(f, "<impossible>"),
        }
    }
}

impl ValueReduction {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    // if we know a variable is either `a` OR `b`, then our overall
    // knowledge is `a.union(b)`
    pub fn union(&self, b: &Self) -> Self {
        use ValueReduction::*;
        match (self, b) {
            (Unknown, _) => Unknown,
            (_, Unknown) => Unknown,

            (l, Impossible) => l.clone(),
            (Impossible, r) => r.clone(),

            (Boolean(_), FieldElement(_)) => Unknown,
            (FieldElement(_), Boolean(_)) => Unknown,

            (FieldElement(av), FieldElement(bv)) if av == bv => FieldElement(av.clone()),
            (FieldElement(_), FieldElement(_)) => FieldElement(None),

            (Boolean(av), Boolean(bv)) if av == bv => Boolean(av.clone()),
            (Boolean(_), Boolean(_)) => Boolean(None),
        }
    }

    // if we know a variable is both `a` AND `b`, then our overall
    // knowledge is `a.intersect(b)`
    pub fn intersect(&self, b: &Self) -> Self {
        use ValueReduction::*;

        let bool_felt_merge = |b: &Option<bool>, fe: &Option<BigInt>| match (b, fe) {
            // TODO: does this make sense? Should `true` be treated as
            // incompatible with `1`? It seems like it shouldn't be.
            (Some(false), Some(n)) if n.is_zero() => Unknown,
            (Some(true), Some(n)) if n == &BigInt::from_bytes_le(Sign::Plus, &[1]) => Unknown,
            (Some(_), Some(_)) => Impossible,
            _ => Unknown,
        };

        match (self, b) {
            (Unknown, r) => r.clone(),
            (l, Unknown) => l.clone(),

            (_, Impossible) => Impossible,
            (Impossible, _) => Impossible,

            (Boolean(b), FieldElement(fe)) => bool_felt_merge(b, fe),
            (FieldElement(fe), Boolean(b)) => bool_felt_merge(b, fe),

            (FieldElement(av), FieldElement(bv)) if av == bv => FieldElement(av.clone()),
            (FieldElement(_), FieldElement(_)) => Impossible,

            (Boolean(av), Boolean(bv)) if av == bv => Boolean(av.clone()),
            (Boolean(_), Boolean(_)) => Impossible,
        }
    }

    /// Restricts the value of the node. Returns `true` on the first update.
    #[must_use]
    pub fn set_reduces_to(&mut self, reduces_to: ValueReduction) -> bool {
        let new_val = self.intersect(&reduces_to);
        let result = self != &new_val;
        *self = new_val;
        result
    }

    /// Returns `true` if the value of the node is known.
    #[must_use]
    pub fn is_constant(&self) -> bool {
        match self {
            Self::FieldElement(Some(_)) => true,
            Self::Boolean(Some(_)) => true,
            _ => false,
        }
    }

    /// Returns `true` if the value of the node is a boolean.
    #[must_use]
    pub fn is_boolean(&self) -> bool {
        matches!(self, ValueReduction::Boolean(_))
    }

    /// Returns `true` if the value of the node is a field element.
    #[must_use]
    pub fn is_field_element(&self) -> bool {
        matches!(self, ValueReduction::FieldElement(_))
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;

    use crate::ir::value_meta::ValueReduction;

    #[test]
    fn test_value_knowledge() {
        use ValueReduction::*;
        let mut value = ValueReduction::new();
        assert!(matches!(value, Unknown));

        let number = ValueReduction::FieldElement(Some(BigInt::from(1)));
        assert!(value.set_reduces_to(number));
        assert!(matches!(value, ValueReduction::FieldElement(Some(_))));
        assert!(value.is_field_element());
        assert!(!value.is_boolean());

        let boolean = ValueReduction::Boolean(Some(true));
        assert!(value.set_reduces_to(boolean));
        assert!(matches!(value, ValueReduction::Unknown));
    }
}
