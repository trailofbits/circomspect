use circomspect_program_structure::report_code::ReportCode;

const CODES: &[(&str, ReportCode)] = &[
    ("ParseFail", ReportCode::ParseFail),
    ("CompilerVersionError", ReportCode::CompilerVersionError),
    ("WrongTypesInAssignOperation", ReportCode::WrongTypesInAssignOperation),
    ("WrongArityUnspecified", ReportCode::WrongArityUnspecified),
    ("UndefinedFunction", ReportCode::UndefinedFunction),
    ("UndefinedTemplate", ReportCode::UndefinedTemplate),
    ("SameFunctionDeclaredTwice", ReportCode::SameFunctionDeclaredTwice),
    ("SameTemplateDeclaredTwice", ReportCode::SameTemplateDeclaredTwice),
    ("SameSymbolDeclaredTwice", ReportCode::SameSymbolDeclaredTwice),
    ("ForbiddenDeclarationInFunction", ReportCode::ForbiddenDeclarationInFunction),
    ("NonExistentSymbol", ReportCode::NonExistentSymbol),
    ("NoCompilerVersionWarning", ReportCode::NoCompilerVersionWarning),
    ("MultipleMainInComponent", ReportCode::MultipleMainInComponent),
    ("TemplateWithReturnStatement", ReportCode::TemplateWithReturnStatement),
    ("InvalidArgumentInCall", ReportCode::InvalidArgumentInCall),
    ("InvalidArrayAccess", ReportCode::InvalidArrayAccess),
    ("InvalidSignalAccess", ReportCode::InvalidSignalAccess),
    ("InvalidTag", ReportCode::InvalidTag),
    ("InputTagAccess", ReportCode::InputTagAccess),
    ("InvalidTagAfterArray", ReportCode::InvalidTagAfterArray),
    ("InvalidArraySize", ReportCode::InvalidArraySize),
    ("InvalidArrayIndexBus", ReportCode::InvalidArrayIndexBus),
    ("ConstraintGeneratorInFunction", ReportCode::ConstraintGeneratorInFunction),
    ("RuntimeError", ReportCode::RuntimeError),
    ("NonConstantArrayLength", ReportCode::NonConstantArrayLength),
    ("NonComputableExpression", ReportCode::NonComputableExpression),
    ("WrongBusAssignment", ReportCode::WrongBusAssignment),
    ("WrongAssignmentExpression", ReportCode::WrongAssignmentExpression),
    ("WrongAssignmentRank", ReportCode::WrongAssignmentRank),
    ("AnonymousComponentError", ReportCode::AnonymousComponentError),
    ("UnconstrainedSignal", ReportCode::UnconstrainedSignal),
    ("ShadowingVariable", ReportCode::ShadowingVariable),
    ("ParameterNameCollision", ReportCode::ParameterNameCollision),
    ("FieldElementComparison", ReportCode::FieldElementComparison),
    ("FieldElementArithmetic", ReportCode::FieldElementArithmetic),
    ("SignalAssignmentStatement", ReportCode::SignalAssignmentStatement),
    ("UnusedVariableValue", ReportCode::UnusedVariableValue),
    ("UnusedParameterValue", ReportCode::UnusedParameterValue),
    ("VariableWithoutSideEffect", ReportCode::VariableWithoutSideEffect),
    ("ConstantBranchCondition", ReportCode::ConstantBranchCondition),
    ("NonStrictBinaryConversion", ReportCode::NonStrictBinaryConversion),
    ("CyclomaticComplexity", ReportCode::CyclomaticComplexity),
    ("TooManyArguments", ReportCode::TooManyArguments),
    ("UnconstrainedLessThan", ReportCode::UnconstrainedLessThan),
    ("UnconstrainedDivision", ReportCode::UnconstrainedDivision),
    ("Bn254SpecificCircuit", ReportCode::Bn254SpecificCircuit),
    ("UnusedOutputSignal", ReportCode::UnusedOutputSignal),
    ("UnresolvedCall", ReportCode::UnresolvedCall),
    ("IncompleteCoverage", ReportCode::IncompleteCoverage),
    ("RedundantWitnessAssignment", ReportCode::RedundantWitnessAssignment),
    ("MissingBusType", ReportCode::MissingBusType),
];

#[test]
fn diagnostic_metadata_matches_the_frozen_public_contract() {
    let rows: Vec<_> = include_str!("fixtures/diagnostic_codes.tsv").lines().collect();
    assert_eq!(rows.len(), CODES.len());
    for ((variant, code), row) in CODES.iter().zip(rows) {
        let fields: Vec<_> = row.split('\t').collect();
        assert_eq!(fields.len(), 4, "{variant}");
        assert_eq!(fields[0], *variant);
        assert_eq!(code.id(), fields[1], "{variant} ID");
        assert_eq!(code.name(), fields[2], "{variant} name");
        let url = if fields[3] == "<none>" { None } else { Some(fields[3]) };
        assert_eq!(code.url().as_deref(), url, "{variant} URL");
    }
}
