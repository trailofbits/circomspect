//! Dependency, side-effect, and output-use warning family.

use super::RuleKind;

pub const KINDS: &[RuleKind] = &[
    RuleKind::UnusedVariableValue,
    RuleKind::UnusedParameterValue,
    RuleKind::SideEffectFreeAssignment,
    RuleKind::UnusedOutputSignal,
];
