//! Certified analysis over typed Circom HIR.

extern crate num_bigint_dig as num_bigint;

pub mod application;
pub mod config;
pub mod hir_cfg;
pub mod hir_facts;
pub mod interprocedural;
pub mod new_rules;
mod scalar_evidence;
