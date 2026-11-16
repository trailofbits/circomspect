// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![cfg_attr(
    test,
    allow(
        clippy::allow_attributes,
        clippy::expect_used,
        clippy::panic,
        clippy::panic_in_result_fn,
        clippy::unwrap_used
    )
)]
//! Circom-independent abstract domains and fixed-point dataflow.

pub mod graph;
pub mod lattice;
pub mod solver;
pub mod timeout;
