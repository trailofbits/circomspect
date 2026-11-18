// Tests intentionally fail by panicking; snapshot assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(clippy::allow_attributes, clippy::expect_used, clippy::panic, clippy::unwrap_used)]

use std::fmt::Write;

use circomspect_parser::frontend::{parse_source, SourceId, Version, VersionPolicy};

#[path = "support/grammar_cases.rs"]
mod grammar_cases;

#[test]
fn complete_parser_contracts_preserve_ast_spans_diagnostics_and_feature_order() {
    let expected = [
        include_str!("fixtures/grammar_contracts/operators.txt"),
        include_str!("fixtures/grammar_contracts/structure.txt"),
        include_str!("fixtures/grammar_contracts/features.txt"),
        include_str!("fixtures/grammar_contracts/recovery.txt"),
        include_str!("fixtures/grammar_contracts/staging.txt"),
        include_str!("fixtures/grammar_contracts/malformed.txt"),
    ];
    for ((name, source), expected) in grammar_cases::CASES.iter().zip(expected) {
        let baseline =
            parse_source(SourceId::new(7), source, VersionPolicy::new(Version::new(2, 2, 3)));
        let mut records = format!("AST: {:#?}\n", baseline.ast);
        for target in grammar_cases::TARGETS {
            let outcome = parse_source(SourceId::new(7), source, VersionPolicy::new(*target));
            assert_eq!(outcome.ast, baseline.ast, "target changed AST: {name}");
            writeln!(
                records,
                "{target:?}: {:#?}",
                (outcome.diagnostics, outcome.pending_feature_checks)
            )
            .unwrap();
        }
        assert_eq!(records, expected, "{name}");
    }
}

fn mixed_expression(steps: &[(u8, u8)]) -> (String, Vec<u8>) {
    let mut expression = "0".to_owned();
    let mut values = vec![0];
    for (kind, value) in steps {
        expression = match kind {
            0 => format!("({expression}+{value})"),
            1 => format!("[{expression},{value}]"),
            2 => format!("F({expression},{value})"),
            3 => {
                values.insert(0, 1);
                format!("(1?{expression}:{value})")
            }
            other => panic!("unknown generated expression kind: {other}"),
        };
        values.push(*value);
    }
    (expression, values)
}

proptest::proptest! {
    #![proptest_config(proptest::test_runner::Config::with_cases(128))]

    #[test]
    fn mixed_expression_operands_keep_source_order(
        steps in proptest::collection::vec((0_u8..4, 2_u8..100), 0..40),
    ) {
        use circomspect_parser::frontend::{SyntaxCategory, WalkSyntax};
        let (expression, expected) = mixed_expression(&steps);
        let source = format!("function F(){{return {expression};}}");
        let parsed = parse_source(SourceId::new(7), &source,
            VersionPolicy::new(Version::new(2, 2, 3)));
        proptest::prop_assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut values = Vec::new();
        parsed.ast.walk_syntax(None, &mut |kind, span, parent| {
            assert!(source.is_char_boundary(span.start()));
            assert!(source.is_char_boundary(span.end()));
            if let Some(parent) = parent {
                assert!(parent.start() <= span.start() && span.end() <= parent.end());
            }
            if kind == SyntaxCategory::Expression {
                if let Ok(value) = source[span.start()..span.end()].parse::<u8>() {
                    values.push(value);
                }
            }
        });
        proptest::prop_assert_eq!(values, expected);
    }
}
