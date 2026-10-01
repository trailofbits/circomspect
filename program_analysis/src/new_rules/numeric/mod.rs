//! Numeric and expression warning family.

use super::{Rule, RuleKind};

pub const KINDS: &[RuleKind] = &[
    RuleKind::BitwiseComplement,
    RuleKind::Bn254SpecificCircuit,
    RuleKind::ConstantConditional,
    RuleKind::FieldArithmetic,
    RuleKind::FieldComparison,
    RuleKind::NonstrictBinaryConversion,
    RuleKind::UnconstrainedDivision,
];

/// Numeric rules enter the registry in this family's declared order.
pub fn rules() -> &'static [&'static dyn Rule] {
    &[]
}
