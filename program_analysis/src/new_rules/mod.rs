//! Certified HIR rules. The legacy analysis registry remains separate until cutover.

mod kind;
mod reporting;
mod result;

pub use kind::RuleKind;
pub use reporting::{Finding, RenderError, SourceMap};
pub use result::{AbstentionReason, RuleResult, ScopedAbstention};
