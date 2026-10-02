//! Read-only evaluation of field-bound normalized equations.

use std::collections::{BTreeMap, BTreeSet};

use num_traits::Signed;

use crate::hir_facts::relations::polynomial::{CurveTag, Monomial, NormalizedEquation};
use crate::hir_facts::{AccessKey, FieldContext, FieldValue};

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
        if self.0.curve != CurveTag::from(field.curve()) {
            return Err(EquationEvaluationError::WrongCurve);
        }
        Ok(())
    }
}

fn assigned_value<'a>(
    field: &FieldContext,
    assignment: &'a BTreeMap<AccessKey, FieldValue>,
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
