//! Direct syntax and maintainability warning family.

use super::{Rule, RuleKind};

pub const KINDS: &[RuleKind] = &[RuleKind::Complexity, RuleKind::TooManyArguments];

/// Direct rules enter the registry in this family's declared order.
pub fn rules() -> &'static [&'static dyn Rule] {
    &[]
}
