// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![cfg_attr(
    test,
    allow(
        clippy::allow_attributes,
        clippy::assert_is_empty,
        clippy::expect_used,
        clippy::format_push_string,
        clippy::panic,
        clippy::panic_in_result_fn,
        clippy::unwrap_used
    )
)]
//! Certified analysis over typed Circom HIR.

extern crate num_bigint_dig as num_bigint;

pub mod application;
pub mod config;
pub mod hir_cfg;
pub mod hir_facts;
pub mod interprocedural;
pub mod new_rules;
mod scalar_evidence;
