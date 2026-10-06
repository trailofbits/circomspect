const DOC_URL: &str = "https://github.com/trailofbits/circomspect/blob/main/doc/analysis_passes.md";

/// Diagnostic codes emitted by the current frontend, semantic checks, and analysis rules.
#[derive(Copy, Clone)]
pub enum ReportCode {
    ParseFail,
    CompilerVersionError,
    WrongTypesInAssignOperation,
    WrongArityUnspecified,
    UndefinedFunction,
    UndefinedTemplate,
    SameFunctionDeclaredTwice,
    SameTemplateDeclaredTwice,
    SameSymbolDeclaredTwice,
    ForbiddenDeclarationInFunction,
    NonExistentSymbol,
    NoCompilerVersionWarning,
    MultipleMainInComponent,
    TemplateWithReturnStatement,
    InvalidArgumentInCall,
    InvalidArrayAccess,
    InvalidSignalAccess,
    InvalidTag,
    InputTagAccess,
    InvalidTagAfterArray,
    InvalidArraySize,
    InvalidArrayIndexBus,
    ConstraintGeneratorInFunction,
    RuntimeError,
    NonConstantArrayLength,
    NonComputableExpression,
    WrongBusAssignment,
    WrongAssignmentExpression,
    WrongAssignmentRank,
    AnonymousComponentError,
    UnconstrainedSignal,
    ShadowingVariable,
    ParameterNameCollision,
    FieldElementComparison,
    FieldElementArithmetic,
    SignalAssignmentStatement,
    UnusedVariableValue,
    UnusedParameterValue,
    VariableWithoutSideEffect,
    ConstantBranchCondition,
    NonStrictBinaryConversion,
    CyclomaticComplexity,
    TooManyArguments,
    UnconstrainedLessThan,
    UnconstrainedDivision,
    Bn254SpecificCircuit,
    UnusedOutputSignal,
    UnresolvedCall,
    IncompleteCoverage,
    RedundantWitnessAssignment,
    MissingBusType,
}

impl ReportCode {
    #[must_use]
    pub fn id(&self) -> String {
        match self {
            Self::ParseFail => "P1000",
            Self::CompilerVersionError => "P1003",
            Self::WrongTypesInAssignOperation => "T2000",
            Self::WrongArityUnspecified => "T20465",
            Self::UndefinedFunction => "T2001",
            Self::UndefinedTemplate => "T2002",
            Self::SameFunctionDeclaredTwice => "T2006",
            Self::SameTemplateDeclaredTwice => "T2007",
            Self::SameSymbolDeclaredTwice => "T2008",
            Self::ForbiddenDeclarationInFunction => "T2016",
            Self::NonExistentSymbol => "T2021",
            Self::NoCompilerVersionWarning => "P1004",
            Self::MultipleMainInComponent => "P1002",
            Self::TemplateWithReturnStatement => "T2024",
            Self::InvalidArgumentInCall => "T2029",
            Self::InvalidArrayAccess => "T2032",
            Self::InvalidSignalAccess => "T2046",
            Self::InvalidTag => "T2048",
            Self::InputTagAccess => "T2048-C",
            Self::InvalidTagAfterArray => "T2049",
            Self::InvalidArraySize => "T2033",
            Self::InvalidArrayIndexBus => "T2053",
            Self::ConstraintGeneratorInFunction => "T2039",
            Self::RuntimeError => "T3001",
            Self::NonConstantArrayLength => "T20463",
            Self::NonComputableExpression => "T20464",
            Self::WrongBusAssignment => "T2059",
            Self::WrongAssignmentExpression => "T2060",
            Self::WrongAssignmentRank => "T2061",
            Self::AnonymousComponentError => "TAC01",
            Self::UnconstrainedSignal => "CA01",
            Self::ShadowingVariable => "CS0001",
            Self::ParameterNameCollision => "CS0002",
            Self::FieldElementComparison => "CS0003",
            Self::FieldElementArithmetic => "CS0004",
            Self::SignalAssignmentStatement => "CS0005",
            Self::UnusedVariableValue => "CS0006",
            Self::UnusedParameterValue => "CS0007",
            Self::VariableWithoutSideEffect => "CS0008",
            Self::ConstantBranchCondition => "CS0009",
            Self::NonStrictBinaryConversion => "CS0010",
            Self::CyclomaticComplexity => "CS0011",
            Self::TooManyArguments => "CS0012",
            Self::UnconstrainedLessThan => "CS0014",
            Self::UnconstrainedDivision => "CS0015",
            Self::Bn254SpecificCircuit => "CS0016",
            Self::UnusedOutputSignal => "CS0018",
            Self::UnresolvedCall => "CS0019",
            Self::IncompleteCoverage => "CS0020",
            Self::RedundantWitnessAssignment => "CS0021",
            Self::MissingBusType => "CS0022",
        }
        .to_string()
    }

    #[must_use]
    pub fn name(&self) -> String {
        match self {
            Self::ParseFail => "parse-fail",
            Self::CompilerVersionError => "compiler-version-error",
            Self::WrongTypesInAssignOperation => "wrong-types-in-assign-operation",
            Self::WrongArityUnspecified => "wrong-number-of-arguments",
            Self::UndefinedFunction => "undefined-function",
            Self::UndefinedTemplate => "undefined-template",
            Self::SameFunctionDeclaredTwice => "same-function-declared-twice",
            Self::SameTemplateDeclaredTwice => "same-template-declared-twice",
            Self::SameSymbolDeclaredTwice => "same-symbol-declared-twice",
            Self::ForbiddenDeclarationInFunction => "forbidden-declaration-in-function",
            Self::NonExistentSymbol => "non-existent-symbol",
            Self::NoCompilerVersionWarning => "no-compiler-version-warning",
            Self::MultipleMainInComponent => "multiple-main-in-component",
            Self::TemplateWithReturnStatement => "template-with-return-statement",
            Self::InvalidArgumentInCall => "invalid-argument-in-call",
            Self::InvalidArrayAccess => "invalid-array-access",
            Self::InvalidSignalAccess => "invalid-signal-access",
            Self::InvalidTag => "invalid-tag",
            Self::InputTagAccess => "input-tag-access",
            Self::InvalidTagAfterArray => "invalid-tag-after-array",
            Self::InvalidArraySize => "invalid-array-size",
            Self::InvalidArrayIndexBus => "invalid-array-index-bus",
            Self::ConstraintGeneratorInFunction => "constraint-generator-in-function",
            Self::RuntimeError => "runtime-error",
            Self::NonConstantArrayLength => "non-constant-array-length",
            Self::NonComputableExpression => "non-computable-expression",
            Self::WrongBusAssignment => "wrong-bus-assignment",
            Self::WrongAssignmentExpression => "wrong-assignment-expression",
            Self::WrongAssignmentRank => "wrong-assignment-rank",
            Self::AnonymousComponentError => "anonymous-component-error",
            Self::UnconstrainedSignal => "unconstrained-signal",
            Self::ShadowingVariable => "shadowing-variable",
            Self::ParameterNameCollision => "parameter-name-collision",
            Self::FieldElementComparison => "field-element-comparison",
            Self::FieldElementArithmetic => "field-element-arithmetic",
            Self::SignalAssignmentStatement => "signal-assignment-statement",
            Self::UnusedVariableValue => "unused-variable-value",
            Self::UnusedParameterValue => "unused-parameter-value",
            Self::VariableWithoutSideEffect => "variable-without-side-effect",
            Self::ConstantBranchCondition => "constant-branch-condition",
            Self::NonStrictBinaryConversion => "non-strict-binary-conversion",
            Self::CyclomaticComplexity => "cyclomatic-complexity",
            Self::TooManyArguments => "too-many-arguments",
            Self::UnconstrainedLessThan => "unconstrained-less-than",
            Self::UnconstrainedDivision => "unconstrained-division",
            Self::Bn254SpecificCircuit => "bn254-specific-circuit",
            Self::UnusedOutputSignal => "unused-output-signal",
            Self::UnresolvedCall => "unresolved-call",
            Self::IncompleteCoverage => "incomplete-analysis",
            Self::RedundantWitnessAssignment => "redundant-witness-assignment",
            Self::MissingBusType => "missing-bus-type",
        }
        .to_string()
    }

    #[must_use]
    pub fn url(&self) -> Option<String> {
        match self {
            Self::ParseFail
            | Self::CompilerVersionError
            | Self::WrongTypesInAssignOperation
            | Self::WrongArityUnspecified
            | Self::UndefinedFunction
            | Self::UndefinedTemplate
            | Self::SameFunctionDeclaredTwice
            | Self::SameTemplateDeclaredTwice
            | Self::SameSymbolDeclaredTwice
            | Self::ForbiddenDeclarationInFunction
            | Self::NonExistentSymbol
            | Self::NoCompilerVersionWarning
            | Self::MultipleMainInComponent
            | Self::TemplateWithReturnStatement
            | Self::InvalidArgumentInCall
            | Self::InvalidArrayAccess
            | Self::InvalidSignalAccess
            | Self::InvalidTag
            | Self::InputTagAccess
            | Self::InvalidTagAfterArray
            | Self::InvalidArraySize
            | Self::InvalidArrayIndexBus
            | Self::ConstraintGeneratorInFunction
            | Self::RuntimeError
            | Self::NonConstantArrayLength
            | Self::NonComputableExpression
            | Self::WrongBusAssignment
            | Self::WrongAssignmentExpression
            | Self::WrongAssignmentRank
            | Self::AnonymousComponentError
            | Self::ParameterNameCollision
            | Self::UnresolvedCall
            | Self::MissingBusType => None,
            Self::UnconstrainedSignal => Some("unconstrained-signal"),
            Self::ShadowingVariable => Some("shadowing-variable"),
            Self::FieldElementComparison => Some("field-element-comparison"),
            Self::FieldElementArithmetic => Some("field-element-arithmetic"),
            Self::SignalAssignmentStatement => Some("signal-assignment"),
            Self::UnusedVariableValue | Self::UnusedParameterValue => {
                Some("unused-variable-or-parameter")
            }
            Self::VariableWithoutSideEffect => Some("side-effect-free-assignment"),
            Self::ConstantBranchCondition => Some("constant-branch-condition"),
            Self::NonStrictBinaryConversion => Some("non-strict-binary-conversion"),
            Self::CyclomaticComplexity | Self::TooManyArguments => {
                Some("overly-complex-function-or-template")
            }
            Self::UnconstrainedLessThan => Some("unconstrained-less-than"),
            Self::UnconstrainedDivision => Some("unconstrained-division"),
            Self::Bn254SpecificCircuit => Some("bn254-specific-circuit"),
            Self::UnusedOutputSignal => Some("unused-output-signal"),
            Self::IncompleteCoverage => Some("incomplete-analysis"),
            Self::RedundantWitnessAssignment => Some("redundant-witness-assignment"),
        }
        .map(|section| format!("{DOC_URL}#{section}"))
    }
}
