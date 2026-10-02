use std::cmp::Ordering;

use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};
use program_structure::utils::constants::Curve;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FieldValue(BigInt);

impl FieldValue {
    #[must_use]
    pub fn as_bigint(&self) -> &BigInt {
        &self.0
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FieldContext {
    curve: Curve,
    modulus: BigInt,
}

impl FieldContext {
    /// Select the same field as the compiler configuration.
    #[must_use]
    pub fn for_curve(curve: Curve) -> Self {
        let digits: &[u8] = match curve {
            Curve::Bn254 => {
                b"21888242871839275222246405745257275088548364400416034343698204186575808495617"
            }
            Curve::Bls12_381 => {
                b"52435875175126190479447740508185965837690552500527637822603658699938581184513"
            }
            Curve::Goldilocks => b"18446744069414584321",
        };
        let modulus = digits
            .iter()
            .fold(BigInt::zero(), |value, digit| value * 10 + BigInt::from(digit - b'0'));
        Self { curve, modulus }
    }

    #[must_use]
    pub fn curve(&self) -> &Curve {
        &self.curve
    }

    /// The selected prime as an integer, without field reduction.
    pub(crate) fn modulus(&self) -> &BigInt {
        &self.modulus
    }

    #[must_use]
    pub fn canonical(&self, value: BigInt) -> FieldValue {
        let mut residue = value % &self.modulus;
        if residue.is_negative() {
            residue += &self.modulus;
        }
        FieldValue(residue)
    }

    #[must_use]
    pub fn parse(&self, text: &str) -> Option<FieldValue> {
        let (digits, radix) =
            if let Some(hex) = text.strip_prefix("0x") { (hex, 16) } else { (text, 10) };
        BigInt::parse_bytes(digits.as_bytes(), radix).map(|value| self.canonical(value))
    }

    #[must_use]
    pub fn add(&self, left: &FieldValue, right: &FieldValue) -> FieldValue {
        self.canonical(&left.0 + &right.0)
    }

    #[must_use]
    pub fn subtract(&self, left: &FieldValue, right: &FieldValue) -> FieldValue {
        self.canonical(&left.0 - &right.0)
    }

    #[must_use]
    pub fn multiply(&self, left: &FieldValue, right: &FieldValue) -> FieldValue {
        self.canonical(&left.0 * &right.0)
    }

    /// Evaluate a proved small compile-time exponent in the selected field.
    pub(crate) fn bounded_power(
        &self,
        base: &FieldValue,
        exponent: &FieldValue,
    ) -> Option<FieldValue> {
        let exponent = exponent.0.to_u16()?;
        if exponent > 512 {
            return None;
        }
        Some(FieldValue(base.0.modpow(&BigInt::from(exponent), &self.modulus)))
    }

    /// Invert a nonzero canonical value in the selected prime field.
    pub(crate) fn inverse(&self, value: &FieldValue) -> Option<FieldValue> {
        if self.is_zero(value) {
            return None;
        }
        let exponent = &self.modulus - BigInt::from(2);
        Some(FieldValue(value.0.modpow(&exponent, &self.modulus)))
    }

    #[must_use]
    pub fn negate(&self, value: &FieldValue) -> FieldValue {
        self.canonical(-&value.0)
    }

    #[must_use]
    pub fn is_zero(&self, value: &FieldValue) -> bool {
        value.0.is_zero()
    }

    /// Compare canonical values using Circom's signed half-field ordering.
    #[must_use]
    pub fn compare_signed(&self, left: &FieldValue, right: &FieldValue) -> Ordering {
        let cutoff = &self.modulus / 2 + 1;
        let signed = |value: &FieldValue| {
            if value.0 >= cutoff {
                &value.0 - &self.modulus
            } else {
                value.0.clone()
            }
        };
        signed(left).cmp(&signed(right))
    }
}

#[cfg(test)]
mod tests {
    use program_structure::utils::constants::Curve;

    use crate::hir_facts::field::FieldContext;

    #[test]
    fn nonzero_values_have_multiplicative_inverses_on_each_curve() {
        for curve in [Curve::Bn254, Curve::Bls12_381, Curve::Goldilocks] {
            let field = FieldContext::for_curve(curve);
            let one = field.canonical(1.into());
            let two = field.canonical(2.into());
            let minus_one = field.canonical((-1).into());
            assert!(field.inverse(&field.canonical(0.into())).is_none());
            for value in [&one, &two, &minus_one] {
                let product = field.inverse(value).map(|inverse| field.multiply(value, &inverse));
                assert_eq!(product, Some(one.clone()));
            }
        }
    }
}
