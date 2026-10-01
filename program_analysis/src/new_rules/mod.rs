//! Certified HIR rules. The legacy analysis registry remains separate until cutover.

pub mod constraints;
pub mod direct;
mod kind;
pub mod numeric;
mod reporting;
mod result;
pub mod uses;

pub use kind::RuleKind;
pub use reporting::{Finding, RenderError, SourceMap};
pub use result::{AbstentionReason, RuleResult, ScopedAbstention};
