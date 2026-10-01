use program_structure::report::MessageCategory;
use program_structure::report_code::ReportCode;

/// The fixed new-pipeline rule identity and presentation level.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum RuleKind {
    BitwiseComplement,
    Bn254SpecificCircuit,
    ConstantConditional,
    FieldArithmetic,
    FieldComparison,
    NonstrictBinaryConversion,
    UnconstrainedDivision,
    SignalAssignment,
    RedundantWitnessAssignment,
    UnconstrainedSignal,
    UnconstrainedLessThan,
    UnusedVariableValue,
    UnusedParameterValue,
    SideEffectFreeAssignment,
    UnusedOutputSignal,
    Complexity,
    TooManyArguments,
    IncompleteCoverage,
}

impl RuleKind {
    #[must_use]
    pub const fn code(self) -> ReportCode {
        use RuleKind::*;
        match self {
            BitwiseComplement | FieldArithmetic => ReportCode::FieldElementArithmetic,
            Bn254SpecificCircuit => ReportCode::Bn254SpecificCircuit,
            ConstantConditional => ReportCode::ConstantBranchCondition,
            FieldComparison => ReportCode::FieldElementComparison,
            NonstrictBinaryConversion => ReportCode::NonStrictBinaryConversion,
            UnconstrainedDivision => ReportCode::UnconstrainedDivision,
            SignalAssignment => ReportCode::SignalAssignmentStatement,
            RedundantWitnessAssignment => ReportCode::RedundantWitnessAssignment,
            UnconstrainedSignal => ReportCode::UnconstrainedSignal,
            UnconstrainedLessThan => ReportCode::UnconstrainedLessThan,
            UnusedVariableValue => ReportCode::UnusedVariableValue,
            UnusedParameterValue => ReportCode::UnusedParameterValue,
            SideEffectFreeAssignment => ReportCode::VariableWithoutSideEffect,
            UnusedOutputSignal => ReportCode::UnusedOutputSignal,
            Complexity => ReportCode::CyclomaticComplexity,
            TooManyArguments => ReportCode::TooManyArguments,
            IncompleteCoverage => ReportCode::IncompleteCoverage,
        }
    }

    #[must_use]
    pub const fn category(self) -> MessageCategory {
        use RuleKind::*;
        match self {
            BitwiseComplement | FieldArithmetic | FieldComparison => MessageCategory::Info,
            Bn254SpecificCircuit
            | ConstantConditional
            | NonstrictBinaryConversion
            | UnconstrainedDivision
            | SignalAssignment
            | RedundantWitnessAssignment
            | UnconstrainedSignal
            | UnconstrainedLessThan
            | UnusedVariableValue
            | UnusedParameterValue
            | SideEffectFreeAssignment
            | UnusedOutputSignal
            | Complexity
            | TooManyArguments
            | IncompleteCoverage => MessageCategory::Warning,
        }
    }
}
