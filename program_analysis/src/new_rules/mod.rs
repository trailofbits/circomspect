//! Certified HIR rules and their presentation contract.

pub mod constraints;
mod context;
pub mod direct;
mod kind;
pub mod numeric;
mod reporting;
mod registry;
mod result;
pub mod uses;

pub use kind::RuleKind;
pub use context::{RuleContext, RuleContextError};
pub use reporting::{Finding, RenderError, SourceMap};
pub use registry::{registered_rules, run_registered, Rule, RuleRunError};
pub use result::{AbstentionReason, RuleResult, ScopedAbstention};
