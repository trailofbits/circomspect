use circomspect_parser::new_frontend::{parse_source, SourceId, SyntaxKind, Version, VersionPolicy};
use circomspect_parser::new_frontend::{load_sources, DiagnosticKind, SyntaxNode};
use std::fs;
use std::path::PathBuf;

fn parse(source: &str) -> circomspect_parser::new_frontend::ParseOutcome {
    parse_source(SourceId::new(0), source, VersionPolicy::new(Version::new(2, 2, 3)))
}

fn assert_node_spans(node: &SyntaxNode, source: &str) {
    assert!(source.is_char_boundary(node.span.start()));
    assert!(source.is_char_boundary(node.span.end()));
    assert!(node.span.start() <= node.span.end());
    assert!(node.span.end() <= source.len());
    for child in &node.children {
        assert_node_spans(child, source);
        assert!(child.span.start() >= node.span.start());
        assert!(child.span.end() <= node.span.end());
    }
}

#[test]
fn parses_library_without_main_and_preserves_definition_spans() {
    let source =
        "pragma circom 2.2.3;\nfunction f(x) { return x + 1; }\ntemplate T() { signal input a; }";
    let outcome = parse(source);
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    assert_eq!(outcome.ast.items.len(), 3);
    assert_eq!(outcome.ast.items[1].kind, SyntaxKind::Function);
    assert_eq!(outcome.ast.items[2].kind, SyntaxKind::Template);
    for item in &outcome.ast.items {
        assert_node_spans(item, source);
    }
}

#[test]
fn recovers_at_unambiguous_definition_boundary_without_closing_brace() {
    let source = "function Bad() { var x = ;\nfunction Good() { return 1; }";
    let outcome = parse(source);
    assert!(!outcome.diagnostics.is_empty());
    assert!(outcome
        .ast
        .items
        .iter()
        .any(|item| item.kind == SyntaxKind::Function && item.text.as_deref() == Some("Good")));
}

#[test]
fn rejects_illegal_top_level_order_and_expression_statements() {
    let source = "function F() { 1 + 2; } include \"later.circom\";";
    let outcome = parse(source);
    assert!(outcome
        .diagnostics
        .iter()
        .any(|d| d.kind == DiagnosticKind::Syntax && d.message.contains("anonymous component")));
    assert!(outcome
        .diagnostics
        .iter()
        .any(|d| d.kind == DiagnosticKind::Syntax && d.message.contains("out of order")));
}

#[test]
fn version_policy_is_distinct_from_source_pragma() {
    let source = "pragma circom 2.1.0; bus B() { signal x; }";
    let outcome = parse(source);
    assert!(outcome.diagnostics.iter().any(|d| d.kind == DiagnosticKind::FeatureVersion));
    let outcome = parse_source(
        SourceId::new(0),
        "pragma circom 2.2.4;",
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    assert!(outcome.diagnostics.iter().any(|d| d.kind == DiagnosticKind::UnsupportedVersion));
    let outcome = parse("pragma circom 999999999999999999999999.2.3;");
    assert!(outcome.diagnostics.iter().any(|d| d.kind == DiagnosticKind::InvalidNumber));
}

#[test]
fn random_and_invalid_utf8_sequences_have_valid_utf8_spans() {
    let alphabet = [b'a', b'0', b'{', b'}', b'"', b'/', b'\n', 0xff];
    let mut state = 0x1234_5678_u64;
    for _ in 0..2000 {
        let mut bytes = Vec::new();
        for _ in 0..30 {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            bytes.push(alphabet[(state as usize) % alphabet.len()]);
        }
        let source = String::from_utf8_lossy(&bytes);
        let outcome = parse(&source);
        for item in &outcome.ast.items {
            assert_node_spans(item, &source);
        }
        for diagnostic in &outcome.diagnostics {
            assert!(source.is_char_boundary(diagnostic.span.start()));
            assert!(source.is_char_boundary(diagnostic.span.end()));
            assert!(diagnostic.span.end() <= source.len());
        }
    }
}

#[test]
fn include_loader_keeps_definitions_after_missing_and_cyclic_includes() {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-frontend-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock available")
            .as_nanos(),
    ));
    fs::create_dir(&directory).expect("create test directory");
    let first = directory.join("a.circom");
    let second = directory.join("b.circom");
    fs::write(&first, "include \"b.circom\"; include \"gone.circom\"; function A() { return 1; }")
        .expect("write first source");
    fs::write(&second, "include \"a.circom\"; function B() { return 2; }")
        .expect("write second source");
    let project =
        load_sources(&[PathBuf::from(&first)], &[], VersionPolicy::new(Version::new(2, 2, 3)));
    assert_eq!(project.files.len(), 2);
    assert!(project.diagnostics.iter().any(|d| d.kind == DiagnosticKind::MissingInclude));
    assert!(project.diagnostics.iter().any(|d| d.kind == DiagnosticKind::CyclicInclude));
    assert!(project.files.iter().any(|file| file
        .outcome
        .ast
        .items
        .iter()
        .any(|item| item.text.as_deref() == Some("A"))));
    assert!(project.files.iter().any(|file| file
        .outcome
        .ast
        .items
        .iter()
        .any(|item| item.text.as_deref() == Some("B"))));
    fs::remove_dir_all(directory).expect("remove test directory");
}

#[test]
fn malformed_utf8_file_has_explicit_read_diagnostic() {
    let directory = std::env::temp_dir().join(format!("circomspect-utf8-{}", std::process::id(),));
    fs::create_dir_all(&directory).expect("create test directory");
    let path = directory.join("invalid.circom");
    fs::write(&path, [0xff_u8, 0xfe_u8]).expect("write invalid UTF-8");
    let project = load_sources(&[path], &[], VersionPolicy::new(Version::new(2, 2, 3)));
    assert!(project.files.is_empty());
    assert!(project.diagnostics.iter().any(|d| d.kind == DiagnosticKind::FileRead));
    fs::remove_dir_all(directory).expect("remove test directory");
}

#[test]
fn malformed_definition_does_not_hide_later_library_definition() {
    let outcome = parse("function Bad( { return 0; } function Good() { return 1; }");
    assert!(!outcome.diagnostics.is_empty());
    assert!(outcome
        .ast
        .items
        .iter()
        .any(|item| item.kind == SyntaxKind::Function && item.text.as_deref() == Some("Good")));
    assert!(outcome.ast.items.iter().any(|item| item.kind == SyntaxKind::Error));
}

#[test]
fn arbitrary_unicode_and_malformed_strings_never_panic_or_make_invalid_spans() {
    let examples =
        ["🦀", "\"unterminated", "/* unterminated", "\u{0000}", "α{β}", "0x", "a//🦀\n;", "\"🦀\""];
    for source in examples {
        let outcome = parse(source);
        for diagnostic in &outcome.diagnostics {
            assert!(source.is_char_boundary(diagnostic.span.start()));
            assert!(source.is_char_boundary(diagnostic.span.end()));
            assert!(diagnostic.span.end() <= source.len());
        }
        for item in &outcome.ast.items {
            assert!(source.is_char_boundary(item.span.start()));
            assert!(source.is_char_boundary(item.span.end()));
            assert!(item.span.end() <= source.len());
        }
    }
}

#[test]
fn parses_expression_operators_and_extended_declarations() {
    let cases = [
        "function F(a,b) { var c = a ? b + 1 : b * 2; return c; }",
        "template T() { signal input a; output signal b; b <== a; }",
        "template T() { signal input {binary} a[2]; component c = U(); }",
        "bus B() { signal input x; }",
        "template T() { B() input b; }",
        "template T() { var (a,b) = (1,2); signal (x,y) <== (a,b); }",
        "template T() { for (var i = 0; i < 2; i++) { log(i); } }",
        "template T() { for (i = 0; i < 2; i++) { assert(i); } }",
        "template T() { while (a) { a--; } if (a) b = 1; else b = 2; }",
        "template T() { c = parallel U(); c.out --> x; a === b; }",
        "template T() { var a = U(1)(2); var b = U(1)(x <== 2); }",
        "template T() { var a = [1, U(1)(2)]; }",
        "template extern_c T() { signal input x; }",
    ];
    for case in cases {
        let outcome = parse(case);
        assert!(outcome.diagnostics.is_empty(), "{case}: {:?}", outcome.diagnostics);
    }
}
