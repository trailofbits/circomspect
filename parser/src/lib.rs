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
//! Owned Circom syntax, recovery, resolution, and typed HIR.

#[macro_use]
extern crate lalrpop_util;

pub mod frontend;
pub mod hir;
