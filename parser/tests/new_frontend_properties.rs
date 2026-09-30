use circomspect_parser::new_frontend::{
    load_sources, parse_source, tokenize, DiagnosticKind, DiagnosticLocation, SourceId, Span,
    Version, VersionPolicy, WalkSyntax,
};
use proptest::prelude::*;

fn source_chunk() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("function F() {".to_owned()),
        Just("template T() {".to_owned()),
        Just("pragma circom 2.2.3;".to_owned()),
        Just("template T() { var a = [b]; }".to_owned()),
        Just("/*".to_owned()),
        Just("//".to_owned()),
        Just("\"".to_owned()),
        Just("{".to_owned()),
        Just("}".to_owned()),
        Just(";".to_owned()),
        any::<char>().prop_map(|character| character.to_string()),
    ]
}

fn valid_span(source: &str, span: Span) -> bool {
    source.is_char_boundary(span.start())
        && source.is_char_boundary(span.end())
        && span.start() <= span.end()
        && span.end() <= source.len()
        && span.source() == SourceId::new(7)
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 512, .. ProptestConfig::default() })]

    #[test]
    fn arbitrary_utf8_terminates_and_preserves_nested_spans(
        chunks in prop::collection::vec(source_chunk(), 0..50),
    ) {
        let source = chunks.concat();
        let lexed = tokenize(SourceId::new(7), &source);
        let outcome = parse_source(SourceId::new(7), &source,
            VersionPolicy::new(Version::new(2, 2, 2)));
        let mut valid = true;
        outcome.ast.walk_syntax(None, &mut |_, span, parent| {
            valid &= valid_span(&source, span);
            if let Some(parent) = parent {
                valid &= span.start() >= parent.start();
                valid &= span.end() <= parent.end();
            }
        });
        prop_assert!(valid);
        for token in lexed.tokens {
            prop_assert!(valid_span(&source, token.span));
        }
        for trivia in lexed.trivia {
            prop_assert!(valid_span(&source, trivia.span));
        }
        for check in &outcome.pending_feature_checks {
            prop_assert!(valid_span(&source, check.span));
        }
        for diagnostic in &outcome.diagnostics {
            if let Some(span) = diagnostic.span() {
                prop_assert!(valid_span(&source, span));
            }
        }
    }

    #[test]
    fn invalid_utf8_file_produces_path_diagnostic(
        bytes in prop::collection::vec(any::<u8>(), 1..64)
            .prop_filter("invalid UTF-8", |bytes| std::str::from_utf8(bytes).is_err()),
    ) {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-invalid-utf8-property-{}", std::process::id(),
        ));
        std::fs::create_dir_all(&directory).expect("create test directory");
        let path = directory.join("input.circom");
        std::fs::write(&path, &bytes).expect("write generated source");
        let canonical = std::fs::canonicalize(&path).expect("canonical path");
        let project = load_sources(std::slice::from_ref(&path), &[],
            VersionPolicy::new(Version::new(2, 2, 3)));
        prop_assert!(project.files.is_empty());
        let found = project.diagnostics.iter().any(|diagnostic| {
            diagnostic.kind == DiagnosticKind::FileRead
                && if let DiagnosticLocation::Path(path) = &diagnostic.location {
                    path == &canonical
                } else {
                    false
                }
        });
        prop_assert!(found);
        std::fs::remove_dir_all(directory).expect("remove test directory");
    }
}
