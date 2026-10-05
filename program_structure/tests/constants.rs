// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
#[test]
fn curve_prime_bytes_match_the_published_decimal_constants() {
    use circomspect_program_structure::constants::{Curve, UsefulConstants};

    for (curve, decimal, bits) in [
        (
            Curve::Bn254,
            "21888242871839275222246405745257275088548364400416034343698204186575808495617",
            254,
        ),
        (
            Curve::Bls12_381,
            "52435875175126190479447740508185965837690552500527637822603658699938581184513",
            255,
        ),
        (Curve::Goldilocks, "18446744069414584321", 64),
    ] {
        let constants = UsefulConstants::new(&curve);
        assert_eq!(constants.prime().to_string(), decimal);
        assert_eq!(constants.prime_size(), bits);
    }
}
