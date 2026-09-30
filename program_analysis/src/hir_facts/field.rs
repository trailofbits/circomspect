use std::cmp::Ordering;

use num_bigint::BigInt;
use num_traits::{Signed, Zero};
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
