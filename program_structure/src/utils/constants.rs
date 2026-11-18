use anyhow::{anyhow, Error};
use num_bigint::{BigInt, Sign};
use std::fmt;
use std::str::FromStr;

#[derive(Default, Clone, PartialEq, Eq)]
pub enum Curve {
    #[default] // Used for testing.
    Bn254,
    Bls12_381,
    Goldilocks,
}

impl fmt::Display for Curve {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Curve::{Bn254, Bls12_381, Goldilocks};
        match self {
            Bn254 => write!(f, "BN254"),
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
        use Curve::{Bn254, Bls12_381, Goldilocks};
        match self {
            Bn254 => BigInt::from_bytes_be(
                Sign::Plus,
                &[
                    0x30, 0x64, 0x4e, 0x72, 0xe1, 0x31, 0xa0, 0x29, 0xb8, 0x50, 0x45, 0xb6, 0x81,
                    0x81, 0x58, 0x5d, 0x28, 0x33, 0xe8, 0x48, 0x79, 0xb9, 0x70, 0x91, 0x43, 0xe1,
                    0xf5, 0x93, 0xf0, 0x00, 0x00, 0x01,
                ],
            ),
            Bls12_381 => BigInt::from_bytes_be(
                Sign::Plus,
                &[
                    0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48, 0x33, 0x39, 0xd8, 0x08, 0x09,
                    0xa1, 0xd8, 0x05, 0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe, 0xff, 0xff,
                    0xff, 0xff, 0x00, 0x00, 0x00, 0x01,
                ],
            ),
            Goldilocks => BigInt::from(0xffff_ffff_0000_0001_u64),
        }
    }
}

impl FromStr for Curve {
    type Err = Error;

    fn from_str(curve: &str) -> Result<Self, Self::Err> {
        match &curve.to_uppercase()[..] {
            "BN254" => Ok(Curve::Bn254),
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
    #[must_use]
    pub fn new(curve: &Curve) -> UsefulConstants {
        UsefulConstants { curve: curve.clone(), prime: curve.prime() }
    }

    /// Returns the used curve.
    #[must_use]
    pub fn curve(&self) -> &Curve {
        &self.curve
    }

    /// Returns the used prime.
    #[must_use]
    pub fn prime(&self) -> &BigInt {
        &self.prime
    }

    /// Returns the size in bits of the used prime.
    #[must_use]
    pub fn prime_size(&self) -> usize {
        self.prime.bits()
    }
}
