//! Numeric and expression warning family.

use super::RuleKind;

pub const KINDS: &[RuleKind] = &[
    RuleKind::BitwiseComplement,
    RuleKind::Bn254SpecificCircuit,
    RuleKind::ConstantConditional,
    RuleKind::FieldArithmetic,
    RuleKind::FieldComparison,
    RuleKind::NonstrictBinaryConversion,
    RuleKind::UnconstrainedDivision,
];
