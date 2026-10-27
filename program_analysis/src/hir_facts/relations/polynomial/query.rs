//! Read-only evaluation of field-bound normalized equations.

use std::collections::{BTreeMap, BTreeSet};

use num_traits::Signed;
use num_bigint::BigInt;

use crate::hir_facts::relations::polynomial::{Monomial, NormalizedEquation, QuadraticPolynomial};
use crate::hir_facts::{AccessKey, CurveKey, FieldContext, FieldValue};

/// Why an equation cannot be evaluated against a supplied field assignment.
#[derive(Clone, Debug, Eq, PartialEq, thiserror::Error)]
pub(crate) enum EquationEvaluationError {
    #[error("the equation belongs to a different field")]
    WrongCurve,
    #[error("the equation has no assigned value for {0:?}")]
    MissingValue(AccessKey),
    #[error("the assigned value for {0:?} is not canonical in the selected field")]
    NoncanonicalValue(AccessKey),
}

impl NormalizedEquation {
    /// Compare a field-bound equation with a canonical linear relation.
    ///
    /// Coefficients describe an equation equal to zero; scalar multiples and
    /// rearrangements compare equally through the existing normalization.
    pub(crate) fn matches_linear_relation(
        &self,
        field: &FieldContext,
        constant: BigInt,
        terms: &[(AccessKey, i32)],
    ) -> Result<bool, EquationEvaluationError> {
        self.check_field(field)?;
        let mut polynomial = QuadraticPolynomial::zero(field);
        polynomial.add_term(field, Monomial::Constant, field.canonical(constant));
        for (key, coefficient) in terms {
            polynomial.add_term(
                field,
                Monomial::Linear(key.clone()),
                field.canonical((*coefficient).into()),
            );
        }
        Ok(*self == Self::between(polynomial, QuadraticPolynomial::zero(field), field))
    }

    /// Number of stored canonical terms, available without allocating a support set.
    pub(crate) fn term_count(&self) -> usize {
        self.0.terms.len()
    }

    /// Enumerate the exact signal keys used by the polynomial in stable order.
    ///
    /// Cancelled terms contribute no keys. Source-access validity must be checked
    /// separately before this normalized support is used as complete evidence.
    pub(crate) fn accesses(&self) -> Vec<&AccessKey> {
        let mut keys = BTreeSet::new();
        for monomial in self.0.terms.keys() {
            match monomial {
                Monomial::Constant => {}
                Monomial::Linear(key) => {
                    keys.insert(key);
                }
                Monomial::Quadratic(left, right) => {
                    keys.insert(left);
                    keys.insert(right);
                }
            }
        }
        keys.into_iter().collect()
    }

    /// Evaluate the equation's polynomial in its original field.
    ///
    /// This computes a residue only; zero does not certify source validity or
    /// establish that every generated constraint was checked.
    ///
    /// # Errors
    /// Returns a field mismatch, missing operand, or noncanonical operand value.
    pub(crate) fn evaluate(
        &self,
        field: &FieldContext,
        assignment: &BTreeMap<AccessKey, FieldValue>,
    ) -> Result<FieldValue, EquationEvaluationError> {
        self.evaluate_values(field, assignment)
    }

    fn evaluate_values(
        &self,
        field: &FieldContext,
        assignment: &impl EquationValues,
    ) -> Result<FieldValue, EquationEvaluationError> {
        self.check_field(field)?;
        let mut value = field.canonical(0.into());
        for (monomial, coefficient) in &self.0.terms {
            let term = match monomial {
                Monomial::Constant => coefficient.clone(),
                Monomial::Linear(key) => {
                    let operand = assigned_value(field, assignment, key)?;
                    field.multiply(coefficient, operand)
                }
                Monomial::Quadratic(left, right) => {
                    let left = assigned_value(field, assignment, left)?;
                    let right = assigned_value(field, assignment, right)?;
                    field.multiply(coefficient, &field.multiply(left, right))
                }
            };
            value = field.add(&value, &term);
        }
        Ok(value)
    }

    /// Complete one linear target while keeping every other candidate value fixed.
    ///
    /// Returns no candidate when the target is absent or occurs quadratically.
    /// This supplies a candidate only; source ownership and all generated equations
    /// remain separate obligations of the caller.
    ///
    /// # Errors
    /// Returns a field mismatch, missing operand, or noncanonical operand value.
    pub(crate) fn solve_linear_target(
        &self,
        field: &FieldContext,
        assignment: &BTreeMap<AccessKey, FieldValue>,
        target: &AccessKey,
    ) -> Result<Option<FieldValue>, EquationEvaluationError> {
        self.check_field(field)?;
        let mut coefficient = None;
        for (monomial, value) in &self.0.terms {
            match monomial {
                Monomial::Constant => {}
                Monomial::Linear(key) => {
                    if key == target {
                        coefficient = Some(value);
                    }
                }
                Monomial::Quadratic(left, right) => {
                    if left == target || right == target {
                        return Ok(None);
                    }
                }
            }
        }
        let Some(coefficient) = coefficient else { return Ok(None) };
        let Some(inverse) = field.inverse(coefficient) else { return Ok(None) };
        let values = ZeroTargetValues { assignment, target, zero: field.canonical(0.into()) };
        let remainder = self.evaluate_values(field, &values)?;
        Ok(Some(field.multiply(&field.negate(&remainder), &inverse)))
    }

    /// Solve an equation containing exactly one linear signal and a constant.
    ///
    /// The returned value is a candidate seed. Generated source provenance and
    /// all other equations remain obligations of the caller's closure proof.
    ///
    /// # Errors
    /// Returns a field mismatch before inspecting the equation's shape.
    pub(crate) fn singleton_solution(
        &self,
        field: &FieldContext,
    ) -> Result<Option<(AccessKey, FieldValue)>, EquationEvaluationError> {
        self.check_field(field)?;
        let mut constant = field.canonical(0.into());
        let mut linear = None;
        for (monomial, coefficient) in &self.0.terms {
            match monomial {
                Monomial::Constant => constant = coefficient.clone(),
                Monomial::Linear(key) => {
                    if linear.replace((key, coefficient)).is_some() {
                        return Ok(None);
                    }
                }
                Monomial::Quadratic(_, _) => return Ok(None),
            }
        }
        let Some((key, coefficient)) = linear else { return Ok(None) };
        let Some(inverse) = field.inverse(coefficient) else { return Ok(None) };
        let value = field.multiply(&field.negate(&constant), &inverse);
        Ok(Some((key.clone(), value)))
    }

    fn check_field(&self, field: &FieldContext) -> Result<(), EquationEvaluationError> {
        if self.0.curve != CurveKey::from(field.curve()) {
            return Err(EquationEvaluationError::WrongCurve);
        }
        Ok(())
    }
}

trait EquationValues {
    fn get(&self, key: &AccessKey) -> Option<&FieldValue>;
}

impl EquationValues for BTreeMap<AccessKey, FieldValue> {
    fn get(&self, key: &AccessKey) -> Option<&FieldValue> {
        BTreeMap::get(self, key)
    }
}

struct ZeroTargetValues<'a> {
    assignment: &'a BTreeMap<AccessKey, FieldValue>,
    target: &'a AccessKey,
    zero: FieldValue,
}

impl EquationValues for ZeroTargetValues<'_> {
    fn get(&self, key: &AccessKey) -> Option<&FieldValue> {
        if key == self.target {
            Some(&self.zero)
        } else {
            self.assignment.get(key)
        }
    }
}

fn assigned_value<'a>(
    field: &FieldContext,
    assignment: &'a impl EquationValues,
    key: &AccessKey,
) -> Result<&'a FieldValue, EquationEvaluationError> {
    let value =
        assignment.get(key).ok_or_else(|| EquationEvaluationError::MissingValue(key.clone()))?;
    if value.as_bigint().is_negative() || value.as_bigint() >= field.modulus() {
        return Err(EquationEvaluationError::NoncanonicalValue(key.clone()));
    }
    Ok(value)
}

#[cfg(test)]
mod tests;
