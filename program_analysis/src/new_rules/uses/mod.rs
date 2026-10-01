//! Dependency, side-effect, and output-use warning family.

use crate::new_rules::{Rule, RuleKind};

pub const KINDS: &[RuleKind] = &[
    RuleKind::UnusedVariableValue,
    RuleKind::UnusedParameterValue,
    RuleKind::SideEffectFreeAssignment,
    RuleKind::UnusedOutputSignal,
];

/// Use and effect rules enter the registry in this family's declared order.
pub fn rules() -> &'static [&'static dyn Rule] {
    &[]
}
