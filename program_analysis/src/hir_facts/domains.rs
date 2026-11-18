//! Finite-height fact domains used by the HIR providers.

use abstract_interpretation::lattice::Lattice;

use super::field::FieldValue;

/// Field-aware exact value or the canonical field range.
///
/// This flat domain has height three: unreachable, one exact value, canonical.
///
/// `Unreachable` is bottom; each `Exact` value is below `Canonical`.
/// Equal exact values join to themselves; different exact values join to `Canonical`.
/// Exact values store canonical integers interpreted in the selected field. The analysis and
/// context carry that field's identity; `FieldValue` does not. Transfers use the selected field
/// and leave unknown values canonical.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FieldRange {
    Unreachable,
    Exact(FieldValue),
    Canonical,
}

impl Lattice for FieldRange {
    fn bottom() -> Self {
        Self::Unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unreachable, _) | (_, Self::Canonical) => true,
            (Self::Exact(left), Self::Exact(right)) => left == right,
            (Self::Exact(_), Self::Unreachable) | (Self::Canonical, _) => false,
        }
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        if other.leq(self) {
            return false;
        }
        if let Self::Unreachable = self {
            *self = other.clone();
        } else {
            *self = Self::Canonical;
        }
        true
    }
}

/// A sound upper bound for polynomial degree in witness inputs.
///
/// Its five-element chain saturates at `Unbounded`; no widening is needed.
///
/// The order is `Unreachable < Constant < Linear < Quadratic < Unbounded`; join takes the
/// maximum. Transfer functions must preserve source-form degree evidence: numeric cancellation
/// alone cannot certify the source form of a constraint.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DegreeUpper {
    Unreachable,
    Constant,
    Linear,
    Quadratic,
    Unbounded,
}

impl DegreeUpper {
    #[must_use]
    pub const fn multiply(self, other: Self) -> Self {
        use DegreeUpper::{Constant, Linear, Quadratic, Unbounded, Unreachable};
        match (self, other) {
            (Unreachable, _) | (_, Unreachable) => Unreachable,
            (Constant, degree) | (degree, Constant) => degree,
            (Linear, Linear) => Quadratic,
            (Linear | Quadratic | Unbounded, Linear | Quadratic | Unbounded) => Unbounded,
        }
    }
}

impl Lattice for DegreeUpper {
    fn bottom() -> Self {
        Self::Unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        *self <= *other
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        if *self >= *other {
            return false;
        }
        *self = *other;
        true
    }
}
