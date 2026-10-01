//! Constraint and signal warning family.

use crate::new_rules::{Rule, RuleKind};

pub const KINDS: &[RuleKind] = &[
    RuleKind::SignalAssignment,
    RuleKind::RedundantWitnessAssignment,
    RuleKind::UnconstrainedSignal,
    RuleKind::UnconstrainedLessThan,
];

/// Constraint rules enter the registry in this family's declared order.
pub fn rules() -> &'static [&'static dyn Rule] {
    &[]
}
