//! Small reusable abstract domains. Analyses own their domain interpretation.

use std::collections::BTreeSet;
use std::sync::Arc;

/// A join-semilattice with a least element.
///
/// Implementations must make `join_assign` the least upper bound, returning
/// `true` exactly when `self` changes. These laws are checked in property tests.
/// Rust checks the interface, not these laws: implementations must preserve reflexive/transitive
/// order and an associative, commutative, idempotent join consistent with `leq`.
pub trait Lattice: Clone + Eq {
    fn bottom() -> Self;
    fn leq(&self, other: &Self) -> bool;
    fn join_assign(&mut self, other: &Self) -> bool;
}

/// Share immutable domain snapshots, copying only when incomparable states join.
///
/// The underlying lattice owns the order and join. Comparable states reuse the
/// existing upper bound; mutation through `Arc::make_mut` preserves prior snapshots.
impl<T: Lattice> Lattice for Arc<T> {
    fn bottom() -> Self {
        Self::new(T::bottom())
    }

    fn leq(&self, other: &Self) -> bool {
        Self::ptr_eq(self, other) || self.as_ref().leq(other.as_ref())
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        if other.leq(self) {
            return false;
        }
        if self.leq(other) {
            *self = other.clone();
            return true;
        }
        Self::make_mut(self).join_assign(other.as_ref())
    }
}

/// Facts ordered by subset inclusion.
///
/// Empty is bottom, subset inclusion is the order, and union is the least upper bound.
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
///
/// `Unreachable` is bottom and `Reachable` is top; join selects the reached state.
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
///
/// `Bottom` is below each `Value`, with `Top` above all values. Equal values join unchanged;
/// different values join to `Top`.
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
