use circomspect_parser::new_frontend::{
    load_sources, parse_source, DefinitionKind, DiagnosticKind, DiagnosticLocation, Expression,
    Item, SourceId, Statement, SyntaxCategory, Version, VersionPolicy, WalkSyntax,
};
use std::fs;

fn parse(source: &str) -> circomspect_parser::new_frontend::ParseOutcome {
    parse_source(SourceId::new(0), source, VersionPolicy::new(Version::new(2, 2, 3)))
}

fn has_definition(outcome: &circomspect_parser::new_frontend::ParseOutcome, name: &str) -> bool {
    outcome.ast.items.iter().any(|item| {
        if let Item::Definition(definition) = item {
            definition.name.name == name
        } else {
            false
        }
    })
}

fn assert_spans(source: &str, outcome: &circomspect_parser::new_frontend::ParseOutcome) {
    outcome.ast.walk_syntax(None, &mut |_, span, parent| {
        assert!(source.is_char_boundary(span.start()));
        assert!(source.is_char_boundary(span.end()));
        assert!(span.start() <= span.end());
        assert!(span.end() <= source.len());
        if let Some(parent) = parent {
            assert!(span.start() >= parent.start());
            assert!(span.end() <= parent.end());
            assert_eq!(span.source(), parent.source());
        }
    });
    for diagnostic in &outcome.diagnostics {
        if let Some(span) = diagnostic.span() {
            assert!(source.is_char_boundary(span.start()));
            assert!(source.is_char_boundary(span.end()));
            assert!(span.end() <= source.len());
        }
    }
}

#[test]
fn parses_library_without_main_and_preserves_definition_spans() {
    let source =
        "pragma circom 2.2.3;\nfunction f(x) { return x + 1; }\ntemplate T() { signal input a; }";
    let outcome = parse(source);
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    assert_eq!(outcome.ast.items.len(), 3);
    assert!(has_definition(&outcome, "f"));
    assert!(has_definition(&outcome, "T"));
    assert_spans(source, &outcome);
}

#[test]
fn malformed_definition_does_not_hide_later_library_definition() {
    let source = "function Bad( { return 0; } function Good() { return 1; }";
    let outcome = parse(source);
    assert!(!outcome.diagnostics.is_empty());
    assert!(has_definition(&outcome, "Good"));
    let errors = outcome.ast.items.iter().filter_map(|item| {
        let Item::Error { span } = item else {
            return None;
        };
        Some(span)
    });
    assert!(errors.count() > 0);
    assert_spans(source, &outcome);
}

#[test]
fn recovers_at_unambiguous_definition_boundary_without_closing_brace() {
    let source = "function Bad() { var x = ;\nfunction Good() { return 1; }";
    let outcome = parse(source);
    assert!(!outcome.diagnostics.is_empty());
    assert!(has_definition(&outcome, "Good"));
    assert_spans(source, &outcome);
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
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    let outcome = parse_source(SourceId::new(0), source, VersionPolicy::new(Version::new(2, 1, 0)));
    assert!(outcome.diagnostics.iter().any(|d| d.kind == DiagnosticKind::FeatureVersion));
    let source = "pragma circom 2.2.0; template extern_c T() {}";
    let outcome = parse_source(SourceId::new(0), source, VersionPolicy::new(Version::new(2, 2, 0)));
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
fn inline_array_bus_types_remain_pending_without_name_resolution() {
    let source = include_str!("../../tests/conformance/cases/inline_array_buses_valid.circom")
        .replacen("pragma circom 2.2.3", "pragma circom 2.2.2", 1);
    let outcome =
        parse_source(SourceId::new(0), &source, VersionPolicy::new(Version::new(2, 2, 2)));
    assert!(
        outcome
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.kind != DiagnosticKind::FeatureVersion),
        "{:?}",
        outcome.diagnostics
    );
    assert!(outcome.pending_feature_checks.iter().any(|check| {
        &source[check.span.start()..check.span.end()] == "[a[2], a[0], a[1]]"
            && check.required_version == Version::new(2, 2, 3)
    }));
    assert_spans(&source, &outcome);
}

#[test]
fn parallel_operand_preserves_binary_expression() {
    let source = "template T() { component c = parallel U(1) + V(2); }";
    let outcome = parse(source);
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    let Item::Definition(definition) = &outcome.ast.items[0] else {
        panic!("definition");
    };
    let Statement::Declaration(declaration) = &definition.body.statements[0] else {
        panic!("declaration");
    };
    let Some((_, Expression::Parallel { operand, .. })) = &declaration.symbols[0].initialization
    else {
        panic!("parallel initializer");
    };
    let Expression::Binary { operator, left, right, span } = operand.as_ref() else {
        panic!("binary parallel operand");
    };
    assert!(left.span().start() < right.span().start());
    assert!(span.start() < span.end());
    assert_eq!(*operator, circomspect_parser::new_frontend::BinaryOperator::Add);
    assert_spans(source, &outcome);
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
        assert_spans(case, &outcome);
    }
}

#[test]
fn source_ast_has_no_untyped_nodes_for_valid_examples() {
    let source = "function F() { return 1; } template T() { signal input x; }";
    let outcome = parse(source);
    assert!(outcome.diagnostics.is_empty());
    let mut categories = Vec::new();
    outcome.ast.walk_syntax(None, &mut |category, _, _| categories.push(category));
    assert!(categories.contains(&SyntaxCategory::Definition));
    assert!(categories.contains(&SyntaxCategory::Statement));
    assert!(categories.contains(&SyntaxCategory::Declaration));
    assert!(categories.contains(&SyntaxCategory::Expression));
    assert!(categories.contains(&SyntaxCategory::Identifier));
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
    let project = load_sources(&[first], &[], VersionPolicy::new(Version::new(2, 2, 3)));
    assert_eq!(project.files.len(), 2);
    assert!(project.diagnostics.iter().any(|d| d.kind == DiagnosticKind::MissingInclude));
    assert!(project.diagnostics.iter().any(|d| d.kind == DiagnosticKind::CyclicInclude));
    assert!(project.files.iter().any(|file| has_definition(&file.outcome, "A")));
    assert!(project.files.iter().any(|file| has_definition(&file.outcome, "B")));
    fs::remove_dir_all(directory).expect("remove test directory");
}

#[test]
fn malformed_utf8_file_has_path_located_read_diagnostic() {
    let directory = std::env::temp_dir().join(format!("circomspect-utf8-{}", std::process::id()));
    fs::create_dir_all(&directory).expect("create test directory");
    let path = directory.join("invalid.circom");
    fs::write(&path, [0xff_u8, 0xfe_u8]).expect("write invalid UTF-8");
    let canonical = fs::canonicalize(&path).expect("canonical source path");
    let project =
        load_sources(std::slice::from_ref(&path), &[], VersionPolicy::new(Version::new(2, 2, 3)));
    assert!(project.files.is_empty());
    assert!(project.diagnostics.iter().any(|d| d.kind == DiagnosticKind::FileRead
        && if let DiagnosticLocation::Path(location) = &d.location {
            location == &canonical
        } else {
            false
        }));
    fs::remove_dir_all(directory).expect("remove test directory");
}

#[test]
fn arbitrary_unicode_and_malformed_strings_never_panic_or_make_invalid_spans() {
    let examples = [
        "🦀",
        "\"unterminated",
        "/* unterminated",
        "\u{0000}",
        "α{β}",
        "0x",
        "a//🦀\n;",
        "\"🦀\"",
        "_0x",
    ];
    for source in examples {
        let outcome = parse(source);
        assert_spans(source, &outcome);
    }
}

#[test]
fn typed_ast_distinguishes_definition_and_direction_kinds() {
    let outcome = parse("template T() { output signal x; signal input y; }");
    assert!(outcome.diagnostics.is_empty());
    let Item::Definition(definition) = &outcome.ast.items[0] else {
        panic!("definition");
    };
    let DefinitionKind::Template { custom, external, parallel } = definition.kind else {
        panic!("template kind");
    };
    assert!(!custom && !external && !parallel);
    let Statement::Declaration(first) = &definition.body.statements[0] else {
        panic!("first declaration");
    };
    let Statement::Declaration(second) = &definition.body.statements[1] else {
        panic!("second declaration");
    };
    use circomspect_parser::new_frontend::{DeclarationKind, DirectionSyntax};
    let DeclarationKind::Signal { direction: DirectionSyntax::Before(before), tags: first_tags } =
        &first.kind
    else {
        panic!("direction-first signal");
    };
    let DeclarationKind::Signal { direction: DirectionSyntax::After(after), tags: second_tags } =
        &second.kind
    else {
        panic!("direction-after signal");
    };
    assert!(first_tags.is_empty() && second_tags.is_empty());
    assert_eq!(before.span.start(), 15);
    assert_eq!(after.span.start(), 39);
}
