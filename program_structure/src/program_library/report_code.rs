const DOC_URL: &str = "https://github.com/trailofbits/circomspect/blob/main/doc/analysis_passes.md";

#[derive(Copy, Clone)]
pub enum ReportCode {
    AssertWrongType,
    ParseFail,
    CompilerVersionError,
    WrongTypesInAssignOperation,
    WrongNumberOfArguments(usize, usize),
    WrongArityUnspecified,
    UndefinedFunction,
    UndefinedTemplate,
    UninitializedSymbolInExpression,
    UnableToTypeFunction,
    UnreachableConstraints,
    UnknownIndex,
    UnknownDimension,
    SameFunctionDeclaredTwice,
    SameTemplateDeclaredTwice,
    SameSymbolDeclaredTwice,
    StaticInfoWasOverwritten,
    SignalInLineInitialization,
    SignalOutsideOriginalScope,
    FunctionWrongNumberOfArguments,
    FunctionInconsistentTyping,
    FunctionPathWithoutReturn,
    FunctionReturnError,
    ForbiddenDeclarationInFunction,
    NonHomogeneousArray,
    NonBooleanCondition,
    NonCompatibleBranchTypes,
    NonEqualTypesInExpression,
    NonExistentSymbol,
    NoMainFoundInProject,
    NoCompilerVersionWarning,
    MultipleMainInComponent,
    TemplateCallAsArgument,
    TemplateWrongNumberOfArguments,
    TemplateWithReturnStatement,
    TypeCantBeUseAsCondition,
    EmptyArrayInlineDeclaration,
    PrefixOperatorWithWrongTypes,
    InfixOperatorWithWrongTypes,
    InvalidArgumentInCall,
    InconsistentReturnTypesInBlock,
    InconsistentStaticInformation,
    InvalidArrayAccess,
    InvalidSignalAccess,
    InvalidTag,
    InputTagAccess,
    InvalidTagAfterArray,
    InvalidArraySize,
    InvalidArrayIndexBus,
    InvalidArrayType,
    ForStatementIllConstructed,
    BadArrayAccess,
    AssigningAComponentTwice,
    AssigningASignalTwice,
    NotAllowedOperation,
    ConstraintGeneratorInFunction,
    WrongSignalTags,
    InvalidPartialArray,
    MustBeSingleArithmetic,
    ExpectedDimDiffGotDim(usize, usize),
    RuntimeError,
    UnknownTemplate,
    NonQuadratic,
    NonConstantArrayLength,
    NonComputableExpression,
    WrongBusAssignment,
    WrongAssignmentExpression,
    WrongAssignmentRank,
    AnonymousComponentError,
    TupleError,
    // Constraint analysis codes
    UnconstrainedSignal,
    OneConstraintIntermediate,
    NoOutputInInstance,
    ErrorWat2Wasm,
    // Circomspect specific codes
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
            Self::NoMainFoundInProject => "P1001",
            Self::MultipleMainInComponent => "P1002",
            Self::CompilerVersionError => "P1003",
            Self::NoCompilerVersionWarning => "P1004",
            Self::WrongTypesInAssignOperation => "T2000",
            Self::WrongArityUnspecified | Self::WrongNumberOfArguments(..) => "T20465",
            Self::UndefinedFunction => "T2001",
            Self::UndefinedTemplate => "T2002",
            Self::UninitializedSymbolInExpression => "T2003",
            Self::UnableToTypeFunction => "T2004",
            Self::UnreachableConstraints => "T2005",
            Self::SameFunctionDeclaredTwice => "T2006",
            Self::SameTemplateDeclaredTwice => "T2007",
            Self::SameSymbolDeclaredTwice => "T2008",
            Self::StaticInfoWasOverwritten => "T2009",
            Self::SignalInLineInitialization => "T2010",
            Self::SignalOutsideOriginalScope => "T2011",
            Self::FunctionWrongNumberOfArguments => "T2012",
            Self::FunctionInconsistentTyping => "T2013",
            Self::FunctionPathWithoutReturn => "T2014",
            Self::FunctionReturnError => "T2015",
            Self::ForbiddenDeclarationInFunction => "T2016",
            Self::NonHomogeneousArray => "T2017",
            Self::NonBooleanCondition => "T2018",
            Self::NonCompatibleBranchTypes => "T2019",
            Self::NonEqualTypesInExpression => "T2020",
            Self::NonExistentSymbol => "T2021",
            Self::TemplateCallAsArgument => "T2022",
            Self::TemplateWrongNumberOfArguments => "T2023",
            Self::TemplateWithReturnStatement => "T2024",
            Self::TypeCantBeUseAsCondition => "T2025",
            Self::EmptyArrayInlineDeclaration => "T2026",
            Self::PrefixOperatorWithWrongTypes => "T2027",
            Self::InfixOperatorWithWrongTypes => "T2028",
            Self::InvalidArgumentInCall => "T2029",
            Self::InconsistentReturnTypesInBlock => "T2030",
            Self::InconsistentStaticInformation => "T2031",
            Self::InvalidArrayAccess => "T2032",
            Self::InvalidSignalAccess => "T2046",
            Self::InvalidTag => "T2048",
            Self::InputTagAccess => "T2048-C",
            Self::InvalidTagAfterArray => "T2049",
            Self::InvalidArraySize => "T2033",
            Self::InvalidArrayIndexBus => "T2053",
            Self::InvalidArrayType => "T2034",
            Self::ForStatementIllConstructed | Self::BadArrayAccess => "T2035",
            Self::AssigningAComponentTwice => "T2036",
            Self::AssigningASignalTwice => "T2037",
            Self::NotAllowedOperation => "T2038",
            Self::ConstraintGeneratorInFunction => "T2039",
            Self::WrongSignalTags => "T2040",
            Self::AssertWrongType => "T2041",
            Self::UnknownIndex => "T2042",
            Self::InvalidPartialArray => "T2043",
            Self::MustBeSingleArithmetic => "T2044",
            Self::ExpectedDimDiffGotDim(..) => "T2045",
            Self::RuntimeError => "T3001",
            Self::UnknownDimension => "T20460",
            Self::UnknownTemplate => "T20461",
            Self::NonQuadratic => "T20462",
            Self::NonConstantArrayLength => "T20463",
            Self::NonComputableExpression => "T20464",
            Self::WrongBusAssignment => "T2059",
            Self::WrongAssignmentExpression => "T2060",
            Self::WrongAssignmentRank => "T2061",
            Self::AnonymousComponentError => "TAC01",
            Self::TupleError => "TAC02",
            // Constraint analysis codes
            Self::UnconstrainedSignal => "CA01",
            Self::OneConstraintIntermediate => "CA02",
            Self::NoOutputInInstance => "CA03",
            Self::ErrorWat2Wasm => "W01",
            // Circomspect specific codes
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
            Self::AssertWrongType => "assert-wrong-type",
            Self::ParseFail => "parse-fail",
            Self::CompilerVersionError => "compiler-version-error",
            Self::WrongTypesInAssignOperation => "wrong-types-in-assign-operation",
            Self::WrongArityUnspecified | Self::WrongNumberOfArguments(..) => {
                "wrong-number-of-arguments"
            }
            Self::AnonymousComponentError => "anonymous-component-error",
            Self::TupleError => "tuple-error",
            Self::UndefinedFunction => "undefined-function",
            Self::UndefinedTemplate => "undefined-template",
            Self::UninitializedSymbolInExpression => "uninitialized-symbol-in-expression",
            Self::UnableToTypeFunction => "unable-to-type-function",
            Self::UnreachableConstraints => "unreachable-constraints",
            Self::UnknownIndex => "unknown-index",
            Self::UnknownDimension => "unknown-dimension",
            Self::SameFunctionDeclaredTwice => "same-function-declared-twice",
            Self::SameTemplateDeclaredTwice => "same-template-declared-twice",
            Self::SameSymbolDeclaredTwice => "same-symbol-declared-twice",
            Self::StaticInfoWasOverwritten => "static-info-was-overwritten",
            Self::SignalInLineInitialization => "signal-in-line-initialization",
            Self::SignalOutsideOriginalScope => "signal-outside-original-scope",
            Self::FunctionWrongNumberOfArguments => "function-wrong-number-of-arguments",
            Self::FunctionInconsistentTyping => "function-inconsistent-typing",
            Self::FunctionPathWithoutReturn => "function-path-without-return",
            Self::FunctionReturnError => "function-return-error",
            Self::ForbiddenDeclarationInFunction => "forbidden-declaration-in-function",
            Self::NonHomogeneousArray => "non-homogeneous-array",
            Self::NonBooleanCondition => "non-boolean-condition",
            Self::NonCompatibleBranchTypes => "non-compatible-branch-types",
            Self::NonEqualTypesInExpression => "non-equal-types-in-expression",
            Self::NonExistentSymbol => "non-existent-symbol",
            Self::NoMainFoundInProject => "no-main-found-in-project",
            Self::NoCompilerVersionWarning => "no-compiler-version-warning",
            Self::MultipleMainInComponent => "multiple-main-in-component",
            Self::TemplateCallAsArgument => "template-call-as-argument",
            Self::TemplateWrongNumberOfArguments => "template-wrong-number-of-arguments",
            Self::TemplateWithReturnStatement => "template-with-return-statement",
            Self::TypeCantBeUseAsCondition => "type-cant-be-use-as-condition",
            Self::EmptyArrayInlineDeclaration => "empty-array-inline-declaration",
            Self::PrefixOperatorWithWrongTypes => "prefix-operator-with-wrong-types",
            Self::InfixOperatorWithWrongTypes => "infix-operator-with-wrong-types",
            Self::InvalidArgumentInCall => "invalid-argument-in-call",
            Self::InconsistentReturnTypesInBlock => "inconsistent-return-types-in-block",
            Self::InconsistentStaticInformation => "inconsistent-static-information",
            Self::InvalidArrayAccess => "invalid-array-access",
            Self::InvalidSignalAccess => "invalid-signal-access",
            Self::InvalidTag => "invalid-tag",
            Self::InputTagAccess => "input-tag-access",
            Self::InvalidTagAfterArray => "invalid-tag-after-array",
            Self::InvalidArraySize => "invalid-array-size",
            Self::InvalidArrayIndexBus => "invalid-array-index-bus",
            Self::InvalidArrayType => "invalid-array-type",
            Self::ForStatementIllConstructed => "for-statement-ill-constructed",
            Self::BadArrayAccess => "bad-array-access",
            Self::AssigningAComponentTwice => "assigning-a-component-twice",
            Self::AssigningASignalTwice => "assigning-a-signal-twice",
            Self::NotAllowedOperation => "not-allowed-operation",
            Self::ConstraintGeneratorInFunction => "constraint-generator-in-function",
            Self::WrongSignalTags => "wrong-signal-tags",
            Self::InvalidPartialArray => "invalid-partial-array",
            Self::MustBeSingleArithmetic => "must-be-single-arithmetic",
            Self::ExpectedDimDiffGotDim(..) => "expected-dim-diff-got-dim",
            Self::RuntimeError => "runtime-error",
            Self::UnknownTemplate => "unknown-template",
            Self::NonQuadratic => "non-quadratic",
            Self::NonConstantArrayLength => "non-constant-array-length",
            Self::NonComputableExpression => "non-computable-expression",
            Self::WrongBusAssignment => "wrong-bus-assignment",
            Self::WrongAssignmentExpression => "wrong-assignment-expression",
            Self::WrongAssignmentRank => "wrong-assignment-rank",
            Self::UnconstrainedSignal => "unconstrained-signal",
            Self::OneConstraintIntermediate => "one-constraint-intermediate",
            Self::NoOutputInInstance => "no-output-in-instance",
            Self::ErrorWat2Wasm => "error-wat2-wasm",
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
            Self::RedundantWitnessAssignment => Some("redundant-witness-assignment"),
            Self::IncompleteCoverage => Some("incomplete-analysis"),
            Self::UnconstrainedSignal => Some("unconstrained-signal"),
            // We only provide a URL for Circomspect specific issues.
            Self::AssertWrongType
            | Self::ParseFail
            | Self::CompilerVersionError
            | Self::WrongTypesInAssignOperation
            | Self::WrongNumberOfArguments(..)
            | Self::WrongArityUnspecified
            | Self::UndefinedFunction
            | Self::UndefinedTemplate
            | Self::UninitializedSymbolInExpression
            | Self::UnableToTypeFunction
            | Self::UnreachableConstraints
            | Self::UnknownIndex
            | Self::UnknownDimension
            | Self::SameFunctionDeclaredTwice
            | Self::SameTemplateDeclaredTwice
            | Self::SameSymbolDeclaredTwice
            | Self::StaticInfoWasOverwritten
            | Self::SignalInLineInitialization
            | Self::SignalOutsideOriginalScope
            | Self::FunctionWrongNumberOfArguments
            | Self::FunctionInconsistentTyping
            | Self::FunctionPathWithoutReturn
            | Self::FunctionReturnError
            | Self::ForbiddenDeclarationInFunction
            | Self::NonHomogeneousArray
            | Self::NonBooleanCondition
            | Self::NonCompatibleBranchTypes
            | Self::NonEqualTypesInExpression
            | Self::NonExistentSymbol
            | Self::NoMainFoundInProject
            | Self::NoCompilerVersionWarning
            | Self::MultipleMainInComponent
            | Self::TemplateCallAsArgument
            | Self::TemplateWrongNumberOfArguments
            | Self::TemplateWithReturnStatement
            | Self::TypeCantBeUseAsCondition
            | Self::EmptyArrayInlineDeclaration
            | Self::PrefixOperatorWithWrongTypes
            | Self::InfixOperatorWithWrongTypes
            | Self::InvalidArgumentInCall
            | Self::InconsistentReturnTypesInBlock
            | Self::InconsistentStaticInformation
            | Self::InvalidArrayAccess
            | Self::InvalidSignalAccess
            | Self::InvalidTag
            | Self::InputTagAccess
            | Self::InvalidTagAfterArray
            | Self::InvalidArraySize
            | Self::InvalidArrayIndexBus
            | Self::InvalidArrayType
            | Self::ForStatementIllConstructed
            | Self::BadArrayAccess
            | Self::AssigningAComponentTwice
            | Self::AssigningASignalTwice
            | Self::NotAllowedOperation
            | Self::ConstraintGeneratorInFunction
            | Self::WrongSignalTags
            | Self::InvalidPartialArray
            | Self::MustBeSingleArithmetic
            | Self::ExpectedDimDiffGotDim(..)
            | Self::RuntimeError
            | Self::UnknownTemplate
            | Self::NonQuadratic
            | Self::NonConstantArrayLength
            | Self::NonComputableExpression
            | Self::WrongBusAssignment
            | Self::WrongAssignmentExpression
            | Self::WrongAssignmentRank
            | Self::AnonymousComponentError
            | Self::TupleError
            | Self::OneConstraintIntermediate
            | Self::NoOutputInInstance
            | Self::ErrorWat2Wasm
            | Self::ParameterNameCollision
            | Self::UnresolvedCall
            | Self::MissingBusType => None,
        }
        .map(|section| format!("{DOC_URL}#{section}"))
    }
}
