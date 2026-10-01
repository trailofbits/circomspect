//! Direct syntax and maintainability warning family.

use crate::new_rules::{Rule, RuleKind};

pub const KINDS: &[RuleKind] = &[RuleKind::Complexity, RuleKind::TooManyArguments];

/// Direct rules enter the registry in this family's declared order.
pub fn rules() -> &'static [&'static dyn Rule] {
    &[]
}
