//! Small reusable abstract domains. Analyses own their domain interpretation.

use std::collections::BTreeSet;

/// A join-semilattice with a least element.
///
/// Implementations must make `join_assign` the least upper bound, returning
/// `true` exactly when `self` changes. These laws are checked in property tests.
pub trait Lattice: Clone + Eq {
    fn bottom() -> Self;
    fn leq(&self, other: &Self) -> bool;
    fn join_assign(&mut self, other: &Self) -> bool;
}

/// Facts ordered by subset inclusion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Set<T: Ord>(BTreeSet<T>);

impl<T: Ord> Set<T> {
    pub fn insert(&mut self, value: T) -> bool {
        self.0.insert(value)
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.0.iter()
    }
}

impl<T: Clone + Ord> Lattice for Set<T> {
    fn bottom() -> Self {
        Self(BTreeSet::new())
    }

    fn leq(&self, other: &Self) -> bool {
        self.0.is_subset(&other.0)
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        let old_size = self.0.len();
        self.0.extend(other.0.iter().cloned());
        self.0.len() != old_size
    }
}

/// Whether a path has been reached.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Reachability {
    Unreachable,
    Reachable,
}

impl Lattice for Reachability {
    fn bottom() -> Self {
        Self::Unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unreachable, _) | (Self::Reachable, Self::Reachable) => true,
            (Self::Reachable, Self::Unreachable) => false,
        }
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        if *self == Self::Unreachable && *other == Self::Reachable {
            *self = Self::Reachable;
            true
        } else {
            false
        }
    }
}

/// Flat constant domain: absent path, one known value, or conflicting values.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Constant<T> {
    Bottom,
    Value(T),
    Top,
}

impl<T: Clone + Eq> Lattice for Constant<T> {
    fn bottom() -> Self {
        Self::Bottom
    }

    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Top) => true,
            (Self::Value(left), Self::Value(right)) => left == right,
            (Self::Top, _) | (Self::Value(_), Self::Bottom) => false,
        }
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        match (&*self, other) {
            (Self::Bottom, Self::Value(value)) => {
                *self = Self::Value(value.clone());
                true
            }
            (Self::Bottom | Self::Value(_), Self::Top) => {
                *self = Self::Top;
                true
            }
            (Self::Value(left), Self::Value(right)) if left != right => {
                *self = Self::Top;
                true
            }
            _ => false,
        }
    }
}
