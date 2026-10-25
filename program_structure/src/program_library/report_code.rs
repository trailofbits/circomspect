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

struct DiagnosticDescriptor {
    id: &'static str,
    name: &'static str,
    anchor: Option<&'static str>,
}

impl ReportCode {
    fn descriptor(self) -> DiagnosticDescriptor {
        let (id, name, anchor) = match self {
            Self::ParseFail => ("P1000", "parse-fail", None),
            Self::CompilerVersionError => ("P1003", "compiler-version-error", None),
            Self::WrongTypesInAssignOperation => ("T2000", "wrong-types-in-assign-operation", None),
            Self::WrongArityUnspecified => ("T20465", "wrong-number-of-arguments", None),
            Self::UndefinedFunction => ("T2001", "undefined-function", None),
            Self::UndefinedTemplate => ("T2002", "undefined-template", None),
            Self::SameFunctionDeclaredTwice => ("T2006", "same-function-declared-twice", None),
            Self::SameTemplateDeclaredTwice => ("T2007", "same-template-declared-twice", None),
            Self::SameSymbolDeclaredTwice => ("T2008", "same-symbol-declared-twice", None),
            Self::ForbiddenDeclarationInFunction => {
                ("T2016", "forbidden-declaration-in-function", None)
            }
            Self::NonExistentSymbol => ("T2021", "non-existent-symbol", None),
            Self::NoCompilerVersionWarning => ("P1004", "no-compiler-version-warning", None),
            Self::MultipleMainInComponent => ("P1002", "multiple-main-in-component", None),
            Self::TemplateWithReturnStatement => ("T2024", "template-with-return-statement", None),
            Self::InvalidArgumentInCall => ("T2029", "invalid-argument-in-call", None),
            Self::InvalidArrayAccess => ("T2032", "invalid-array-access", None),
            Self::InvalidSignalAccess => ("T2046", "invalid-signal-access", None),
            Self::InvalidTag => ("T2048", "invalid-tag", None),
            Self::InputTagAccess => ("T2048-C", "input-tag-access", None),
            Self::InvalidTagAfterArray => ("T2049", "invalid-tag-after-array", None),
            Self::InvalidArraySize => ("T2033", "invalid-array-size", None),
            Self::InvalidArrayIndexBus => ("T2053", "invalid-array-index-bus", None),
            Self::ConstraintGeneratorInFunction => {
                ("T2039", "constraint-generator-in-function", None)
            }
            Self::RuntimeError => ("T3001", "runtime-error", None),
            Self::NonConstantArrayLength => ("T20463", "non-constant-array-length", None),
            Self::NonComputableExpression => ("T20464", "non-computable-expression", None),
            Self::WrongBusAssignment => ("T2059", "wrong-bus-assignment", None),
            Self::WrongAssignmentExpression => ("T2060", "wrong-assignment-expression", None),
            Self::WrongAssignmentRank => ("T2061", "wrong-assignment-rank", None),
            Self::AnonymousComponentError => ("TAC01", "anonymous-component-error", None),
            Self::UnconstrainedSignal => {
                ("CA01", "unconstrained-signal", Some("unconstrained-signal"))
            }
            Self::ShadowingVariable => ("CS0001", "shadowing-variable", Some("shadowing-variable")),
            Self::ParameterNameCollision => ("CS0002", "parameter-name-collision", None),
            Self::FieldElementComparison => {
                ("CS0003", "field-element-comparison", Some("field-element-comparison"))
            }
            Self::FieldElementArithmetic => {
                ("CS0004", "field-element-arithmetic", Some("field-element-arithmetic"))
            }
            Self::SignalAssignmentStatement => {
                ("CS0005", "signal-assignment-statement", Some("signal-assignment"))
            }
            Self::UnusedVariableValue => {
                ("CS0006", "unused-variable-value", Some("unused-variable-or-parameter"))
            }
            Self::UnusedParameterValue => {
                ("CS0007", "unused-parameter-value", Some("unused-variable-or-parameter"))
            }
            Self::VariableWithoutSideEffect => {
                ("CS0008", "variable-without-side-effect", Some("side-effect-free-assignment"))
            }
            Self::ConstantBranchCondition => {
                ("CS0009", "constant-branch-condition", Some("constant-branch-condition"))
            }
            Self::NonStrictBinaryConversion => {
                ("CS0010", "non-strict-binary-conversion", Some("non-strict-binary-conversion"))
            }
            Self::CyclomaticComplexity => {
                ("CS0011", "cyclomatic-complexity", Some("overly-complex-function-or-template"))
            }
            Self::TooManyArguments => {
                ("CS0012", "too-many-arguments", Some("overly-complex-function-or-template"))
            }
            Self::UnconstrainedLessThan => {
                ("CS0014", "unconstrained-less-than", Some("unconstrained-less-than"))
            }
            Self::UnconstrainedDivision => {
                ("CS0015", "unconstrained-division", Some("unconstrained-division"))
            }
            Self::Bn254SpecificCircuit => {
                ("CS0016", "bn254-specific-circuit", Some("bn254-specific-circuit"))
            }
            Self::UnusedOutputSignal => {
                ("CS0018", "unused-output-signal", Some("unused-output-signal"))
            }
            Self::UnresolvedCall => ("CS0019", "unresolved-call", None),
            Self::IncompleteCoverage => {
                ("CS0020", "incomplete-analysis", Some("incomplete-analysis"))
            }
            Self::RedundantWitnessAssignment => {
                ("CS0021", "redundant-witness-assignment", Some("redundant-witness-assignment"))
            }
            Self::MissingBusType => ("CS0022", "missing-bus-type", None),
        };
        DiagnosticDescriptor { id, name, anchor }
    }

    #[must_use]
    pub fn id(&self) -> String {
        self.descriptor().id.to_owned()
    }

    #[must_use]
    pub fn name(&self) -> String {
        self.descriptor().name.to_owned()
    }

    #[must_use]
    pub fn url(&self) -> Option<String> {
        self.descriptor().anchor.map(|section| format!("{DOC_URL}#{section}"))
    }
}
