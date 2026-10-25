use circomspect_parser::new_frontend::Version;

pub const CASES: &[(&str, &str)] = &[
    ("operators", include_str!("../fixtures/grammar_contracts/operators.circom")),
    ("structure", include_str!("../fixtures/grammar_contracts/structure.circom")),
    ("features", include_str!("../fixtures/grammar_contracts/features.circom")),
    ("recovery", include_str!("../fixtures/grammar_contracts/recovery.circom")),
    ("staging", include_str!("../fixtures/grammar_contracts/staging.circom")),
    ("malformed", include_str!("../fixtures/grammar_contracts/malformed.circom")),
];

pub const TARGETS: &[Version] =
    &[Version::new(2, 0, 5), Version::new(2, 1, 0), Version::new(2, 2, 2), Version::new(2, 2, 3)];
