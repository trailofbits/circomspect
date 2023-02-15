use anyhow::{anyhow, Error};
use num_bigint::BigInt;
use std::fmt;
use std::str::FromStr;

#[derive(Clone, PartialEq, Eq)]
pub enum Curve {
    Bn128,
    Bls12_381,
    Goldilocks,
}

// Used for testing.
impl Default for Curve {
    fn default() -> Self {
        Curve::Bn128
    }
}

impl fmt::Display for Curve {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Curve::*;
        match self {
            Bn128 => write!(f, "BN128"),
            Bls12_381 => write!(f, "BLS12_381"),
            Goldilocks => write!(f, "Goldilocks"),
        }
    }
}

impl fmt::Debug for Curve {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl Curve {
    fn prime(&self) -> BigInt {
        use Curve::*;
        let prime = match self {
            Bn128 => {
                "21888242871839275222246405745257275088548364400416034343698204186575808495617"
            }
            Bls12_381 => {
                "52435875175126190479447740508185965837690552500527637822603658699938581184513"
            }
            Goldilocks => "18446744069414584321",
        };
        BigInt::parse_bytes(prime.as_bytes(), 10).expect("failed to parse prime")
    }
}

impl FromStr for Curve {
    type Err = Error;

    fn from_str(curve: &str) -> Result<Self, Self::Err> {
        match &curve.to_uppercase()[..] {
            "BN128" => Ok(Curve::Bn128),
            "BLS12_381" => Ok(Curve::Bls12_381),
            "GOLDILOCKS" => Ok(Curve::Goldilocks),
            _ => Err(anyhow!("failed to parse curve `{curve}`")),
        }
    }
}

#[derive(Clone)]
pub struct UsefulConstants {
    curve: Curve,
    prime: BigInt,
}

impl UsefulConstants {
    pub fn new(curve: &Curve) -> UsefulConstants {
        UsefulConstants { curve: curve.clone(), prime: curve.prime() }
    }

    /// Returns the used curve.
    pub fn curve(&self) -> &Curve {
        &self.curve
    }

    /// Returns the used prime.
    pub fn prime(&self) -> &BigInt {
        &self.prime
    }

    /// Returns the size in bits of the used prime.
    pub fn prime_size(&self) -> usize {
        self.prime.bits()
    }
}
