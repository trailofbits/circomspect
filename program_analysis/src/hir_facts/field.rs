use num_bigint::BigInt;
use num_traits::{Signed, Zero};

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
    modulus: BigInt,
}

impl FieldContext {
    /// Construct a field context with a positive modulus greater than one.
    pub fn new(modulus: BigInt) -> Option<Self> {
        (modulus > BigInt::from(1)).then_some(Self { modulus })
    }

    #[must_use]
    pub fn bn254() -> Self {
        let modulus =
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617"
                .iter()
                .fold(BigInt::zero(), |value, digit| value * 10 + BigInt::from(digit - b'0'));
        Self { modulus }
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
}
