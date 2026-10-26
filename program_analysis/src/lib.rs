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
//!
//! Start with [`application::analyze_files`] for the complete source-to-report path. It loads
//! sources with [`parser::frontend::load_sources`], lifts them with [`parser::hir::lift_project`],
//! and preserves independent definitions when a library has syntax errors or missing callees.
//! A library does not need `main` to be analyzed.
//!
//! [`hir_cfg::build_cfg`] gives one definition a checked control-flow graph.
//! [`hir_facts::AnalysisFacts`] runs local abstract interpretations and exposes certified values
//! or explicit blockers. [`interprocedural::ProjectAnalysis`] supplies the shared project,
//! selected field, call graph, context evidence, and completed summary caches.
//!
//! [`rules::RuleContext::new`] checks that facts and context evidence belong together;
//! [`rules::run_registered`] then emits findings and typed abstentions in registry order.
//! A certified empty result differs from an unavailable result. Callers must also inspect a
//! certificate's specific coverage: an exact conditional return does not prove termination.
//!
//! The `reading_local`, `reading_component`, and `reading_incomplete_library` examples follow
//! these APIs through a positive case and a nearby refusal or absence case. Run them with
//! `cargo run -p circomspect-program-analysis --example reading_local` (or the other names).
//! `cargo test -p circomspect-program-analysis --examples` checks their assertions.
//!
//! Domain implementations state their order, bottom, and join beside the relevant types.
//! Rust enforces evidence ownership and access to constructors; lattice laws and monotone
//! transfers remain semantic obligations checked by law tests and review.

extern crate num_bigint_dig as num_bigint;

pub mod application;
pub mod config;
pub mod hir_cfg;
pub mod hir_facts;
pub mod interprocedural;
pub mod rules;
mod scalar_evidence;

#[cfg(test)]
mod test_fixtures;
