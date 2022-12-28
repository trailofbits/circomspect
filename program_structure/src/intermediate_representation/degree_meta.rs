use log::trace;
use std::cmp::{Ordering, min, max};
use std::collections::HashMap;
use std::fmt;

use super::{VariableName, VariableType};

/// The degree of an expression.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Degree {
    Constant,
    Linear,
    Quadratic,
    NonQuadratic,
}

// Degrees are linearly ordered.
impl PartialOrd<Degree> for Degree {
    fn partial_cmp(&self, other: &Degree) -> Option<Ordering> {
        use Degree::*;
        match (self, other) {
            // `Constant <= _`
            (Constant, Constant) => Some(Ordering::Equal),
            (Constant, Linear) | (Constant, Quadratic) | (Constant, NonQuadratic) => {
                Some(Ordering::Less)
            }
            // `Linear <= _`
            (Linear, Linear) => Some(Ordering::Equal),
            (Linear, Quadratic) | (Linear, NonQuadratic) => Some(Ordering::Less),
            // `Quadratic <= _`
            (Quadratic, Quadratic) => Some(Ordering::Equal),
            (Quadratic, NonQuadratic) => Some(Ordering::Less),
            // `NonQuadratic <= _`
            (NonQuadratic, NonQuadratic) => Some(Ordering::Equal),
            // All other cases are on the form `_ >= _`.
            _ => Some(Ordering::Greater),
        }
    }
}

// Degrees are linearly ordered.
impl Ord for Degree {
    fn cmp(&self, other: &Degree) -> Ordering {
        // `Degree::partial_cmp` always returns `Some(_)`.
        self.partial_cmp(other).unwrap()
    }
}

impl Degree {
    pub fn add(&self, other: &Degree) -> Degree {
        max(*self, *other)
    }

    pub fn infix_sub(&self, other: &Degree) -> Degree {
        max(*self, *other)
    }

    pub fn mul(&self, other: &Degree) -> Degree {
        use Degree::*;
        match (self, other) {
            (Constant, _) => *other,
            (_, Constant) => *self,
            (Linear, Linear) => Quadratic,
            _ => NonQuadratic,
        }
    }

    pub fn pow(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn div(&self, other: &Degree) -> Degree {
        use Degree::*;
        if *other == Constant {
            *self
        } else {
            NonQuadratic
        }
    }

    pub fn int_div(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn modulo(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn shift_left(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn shift_right(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn lesser(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn greater(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn lesser_eq(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn greater_eq(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }
    pub fn equal(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn not_equal(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn bit_or(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn bit_and(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn bit_xor(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn bool_or(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn bool_and(&self, other: &Degree) -> Degree {
        use Degree::*;
        if (*self, *other) == (Constant, Constant) {
            Constant
        } else {
            NonQuadratic
        }
    }

    pub fn prefix_sub(&self) -> Degree {
        *self
    }

    pub fn complement(&self) -> Degree {
        use Degree::*;
        Quadratic
    }

    pub fn bool_not(&self) -> Degree {
        use Degree::*;
        Quadratic
    }
}

impl fmt::Debug for Degree {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use Degree::*;
        match self {
            Constant => write!(f, "constant"),
            Linear => write!(f, "linear"),
            Quadratic => write!(f, "quadratic"),
            NonQuadratic => write!(f, "non-quadratic"),
        }
    }
}

/// An inclusive range of degrees.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct DegreeRange(Degree, Degree);

impl DegreeRange {
    #[must_use]
    pub fn new(start: Degree, end: Degree) -> DegreeRange {
        DegreeRange(start, end)
    }

    #[must_use]
    pub fn start(&self) -> Degree {
        self.0
    }

    #[must_use]
    pub fn end(&self) -> Degree {
        self.1
    }

    #[must_use]
    pub fn contains(&self, degree: Degree) -> bool {
        self.start() <= degree && degree <= self.end()
    }

    /// Returns true if the upper bound is at most constant.
    #[must_use]
    pub fn is_constant(&self) -> bool {
        self.end() <= Degree::Constant
    }

    /// Returns true if the upper bound is at most linear.
    #[must_use]
    pub fn is_linear(&self) -> bool {
        self.end() <= Degree::Linear
    }

    /// Returns true if the upper bound is at most quadratic.
    #[must_use]
    pub fn is_quadratic(&self) -> bool {
        self.end() <= Degree::Quadratic
    }

    /// Computes the infimum (under inverse inclusion) of `self` and `other`.
    /// Note, if the two ranges overlap this will simply be the union of `self`
    /// and `other`.
    pub fn inf(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange(min(self.start(), other.start()), max(self.end(), other.end()))
    }

    /// Constructs the infimum (under inverse inclusion) of the given degree ranges.
    /// Note, if the ranges overlap this will simply be the union of all the ranges.
    ///
    /// # Panics
    ///
    /// This method will panic if the iterator is empty.
    pub fn iter_inf<'a, T: IntoIterator<Item = &'a DegreeRange>>(ranges: T) -> DegreeRange {
        let mut ranges = ranges.into_iter();
        if let Some(range) = ranges.next() {
            let mut result = range.clone();
            for range in ranges {
                result = result.inf(range);
            }
            result
        } else {
            panic!("iterator must not be empty")
        }
    }

    // If the iterator is not empty and all the ranges are `Some(range)` this
    // method will return the same as `DegreeRange::iter_inf`, otherwise it will
    // return `None`.
    pub fn iter_opt<'a, T: IntoIterator<Item = Option<&'a DegreeRange>>>(
        ranges: T,
    ) -> Option<DegreeRange> {
        let ranges = ranges.into_iter().collect::<Option<Vec<_>>>();
        match ranges {
            Some(ranges) if !ranges.is_empty() => Some(Self::iter_inf(ranges)),
            _ => None,
        }
    }

    pub fn add(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().add(&other.start()), self.end().add(&other.end()))
    }

    pub fn infix_sub(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().infix_sub(&other.start()), self.end().infix_sub(&other.end()))
    }

    pub fn mul(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().mul(&other.start()), self.end().mul(&other.end()))
    }

    pub fn pow(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().pow(&other.start()), self.end().pow(&other.end()))
    }

    pub fn div(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().div(&other.start()), self.end().div(&other.end()))
    }

    pub fn int_div(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().int_div(&other.start()), self.end().int_div(&other.end()))
    }

    pub fn modulo(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().modulo(&other.start()), self.end().modulo(&other.end()))
    }

    pub fn shift_left(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(
            self.start().shift_left(&other.start()),
            self.end().shift_left(&other.end()),
        )
    }

    pub fn shift_right(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(
            self.start().shift_right(&other.start()),
            self.end().shift_right(&other.end()),
        )
    }

    pub fn lesser(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().lesser(&other.start()), self.end().lesser(&other.end()))
    }

    pub fn greater(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().greater(&other.start()), self.end().greater(&other.end()))
    }

    pub fn lesser_eq(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().lesser_eq(&other.start()), self.end().lesser_eq(&other.end()))
    }

    pub fn greater_eq(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(
            self.start().greater_eq(&other.start()),
            self.end().greater_eq(&other.end()),
        )
    }
    pub fn equal(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().equal(&other.start()), self.end().equal(&other.end()))
    }

    pub fn not_equal(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().not_equal(&other.start()), self.end().not_equal(&other.end()))
    }

    pub fn bit_or(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().bit_or(&other.start()), self.end().bit_or(&other.end()))
    }

    pub fn bit_and(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().bit_and(&other.start()), self.end().bit_and(&other.end()))
    }

    pub fn bit_xor(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().bit_xor(&other.start()), self.end().bit_xor(&other.end()))
    }

    pub fn bool_or(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().bool_or(&other.start()), self.end().bool_or(&other.end()))
    }

    pub fn bool_and(&self, other: &DegreeRange) -> DegreeRange {
        DegreeRange::new(self.start().bool_and(&other.start()), self.end().bool_and(&other.end()))
    }

    pub fn prefix_sub(&self) -> DegreeRange {
        DegreeRange::new(self.start().prefix_sub(), self.end().prefix_sub())
    }

    pub fn complement(&self) -> DegreeRange {
        DegreeRange::new(self.start().complement(), self.end().complement())
    }

    pub fn bool_not(&self) -> DegreeRange {
        DegreeRange::new(self.start().bool_not(), self.end().bool_not())
    }
}

// Construct a range containing a single element.
impl From<Degree> for DegreeRange {
    fn from(degree: Degree) -> DegreeRange {
        DegreeRange(degree, degree)
    }
}

impl fmt::Debug for DegreeRange {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "[{:?}, {:?}]", self.start(), self.end())
    }
}

/// This type is used to track degrees of individual variables during degree
/// propagation.
#[derive(Default, Clone)]
pub struct DegreeEnvironment {
    // Even though we assume SSA a single variable may have different degrees
    // because of parameter-dependent control flow. We track the lower and upper
    // bounds of the degree of each variable.
    degree_ranges: HashMap<VariableName, DegreeRange>,
    var_types: HashMap<VariableName, VariableType>,
}

impl DegreeEnvironment {
    pub fn new() -> DegreeEnvironment {
        DegreeEnvironment::default()
    }

    /// Sets the degree range of the given variable. Returns true on first update.
    /// TODO: Should probably take the supremum of the given range and any
    /// existing range.
    pub fn set_degree(&mut self, var: &VariableName, range: &DegreeRange) -> bool {
        if self.degree_ranges.insert(var.clone(), range.clone()).is_none() {
            trace!("setting degree range of `{var:?}` to {range:?}");
            true
        } else {
            false
        }
    }

    /// Sets the type of the given variable.
    pub fn set_type(&mut self, var: &VariableName, var_type: &VariableType) {
        if self.var_types.insert(var.clone(), var_type.clone()).is_none() {
            trace!("setting type of `{var:?}` to `{var_type}`");
        }
    }

    /// Gets the degree range of the given variable.
    #[must_use]
    pub fn degree(&self, var: &VariableName) -> Option<&DegreeRange> {
        self.degree_ranges.get(var)
    }

    /// Returns true if the given variable is a local variable.
    #[must_use]
    pub fn is_local(&self, var: &VariableName) -> bool {
        matches!(self.var_types.get(var), Some(VariableType::Local))
    }
}

pub trait DegreeMeta {
    /// Compute expression degrees for this node and child nodes. Returns true
    /// if the node (or a child node) is updated.
    fn propagate_degrees(&mut self, env: &DegreeEnvironment) -> bool;

    /// Returns an inclusive range the degree of the node may take.
    #[must_use]
    fn degree(&self) -> Option<&DegreeRange>;
}

#[derive(Default, Clone)]
pub struct DegreeKnowledge {
    // The inclusive range the degree of the node may take.
    degree_range: Option<DegreeRange>,
}

impl DegreeKnowledge {
    #[must_use]
    pub fn new() -> DegreeKnowledge {
        DegreeKnowledge::default()
    }

    pub fn set_degree(&mut self, range: &DegreeRange) -> bool {
        let result = self.degree_range.is_none();
        self.degree_range = Some(range.clone());
        result
    }

    #[must_use]
    pub fn degree(&self) -> Option<&DegreeRange> {
        self.degree_range.as_ref()
    }

    /// Returns true if the degree range is known, and the upper bound is
    /// at most constant.
    #[must_use]
    pub fn is_constant(&self) -> bool {
        if let Some(range) = &self.degree_range {
            range.is_constant()
        } else {
            false
        }
    }

    /// Returns true if the degree range is known, and the upper bound is
    /// at most linear.
    #[must_use]
    pub fn is_linear(&self) -> bool {
        if let Some(range) = &self.degree_range {
            range.is_linear()
        } else {
            false
        }
    }

    /// Returns true if the degree range is known, and the upper bound is
    /// at most quadratic.
    #[must_use]
    pub fn is_quadratic(&self) -> bool {
        if let Some(range) = &self.degree_range {
            range.is_quadratic()
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Degree, DegreeKnowledge};

    #[test]
    fn test_value_knowledge() {
        let mut value = DegreeKnowledge::new();
        assert!(value.degree().is_none());
        assert!(!value.is_constant());
        assert!(!value.is_linear());
        assert!(!value.is_quadratic());

        assert!(value.set_degree(&Degree::Constant.into()));
        assert!(value.degree().is_some());
        assert!(value.is_constant());
        assert!(value.is_linear());
        assert!(value.is_quadratic());

        assert!(!value.set_degree(&Degree::Linear.into()));
        assert!(value.degree().is_some());
        assert!(!value.is_constant());
        assert!(value.is_linear());
        assert!(value.is_quadratic());

        assert!(!value.set_degree(&Degree::Quadratic.into()));
        assert!(value.degree().is_some());
        assert!(!value.is_constant());
        assert!(!value.is_linear());
        assert!(value.is_quadratic());

        assert!(!value.set_degree(&Degree::NonQuadratic.into()));
        assert!(value.degree().is_some());
        assert!(!value.is_constant());
        assert!(!value.is_linear());
        assert!(!value.is_quadratic());
    }
}
