// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::assert_is_empty,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use circomspect_parser::frontend::{
    load_sources, parse_source, DefinitionKind, DiagnosticKind, DiagnosticLocation, Expression,
    Item, SourceId, Statement, SyntaxCategory, Version, VersionPolicy, WalkSyntax,
};
use std::fs;

fn parse(source: &str) -> circomspect_parser::frontend::ParseOutcome {
    parse_source(SourceId::new(0), source, VersionPolicy::new(Version::new(2, 2, 3)))
}

fn has_definition(outcome: &circomspect_parser::frontend::ParseOutcome, name: &str) -> bool {
    outcome.ast.items.iter().any(|item| {
        if let Item::Definition(definition) = item {
            definition.name.name == name
        } else {
            false
        }
    })
}

fn assert_missing_return(statement: &Statement) {
    let Statement::Return { value: Expression::Call { name, .. }, .. } = statement else {
        panic!("later return must retain its call");
    };
    assert_eq!(name.name, "Missing");
}

fn assert_spans(source: &str, outcome: &circomspect_parser::frontend::ParseOutcome) {
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
fn malformed_statement_preserves_later_statements_and_definitions() {
    let source = "function F() { var a = ; var b = 1; return b; } function G() { return 2; }";
    let outcome = parse(source);
    assert!(outcome
        .diagnostics
        .iter()
        .any(|diagnostic| { diagnostic.kind == DiagnosticKind::Syntax }));
    let Item::Definition(first) = &outcome.ast.items[0] else {
        panic!("first definition");
    };
    assert_eq!(first.name.name, "F");
    let Statement::Error { span } = &first.body.statements[0] else {
        panic!("error statement");
    };
    assert_eq!(&source[span.start()..span.end()], "var a = ;");
    let Statement::Declaration(_) = &first.body.statements[1] else {
        panic!("later declaration");
    };
    let Statement::Return { .. } = &first.body.statements[2] else {
        panic!("later return");
    };
    assert!(has_definition(&outcome, "G"));
    assert_spans(source, &outcome);
}

#[test]
fn nested_statement_recovery_stops_at_semicolon_inside_its_block() {
    let source = "function F() { if (1) { var a = ; var b = 2; } return 3; }";
    let outcome = parse(source);
    assert!(outcome
        .diagnostics
        .iter()
        .any(|diagnostic| { diagnostic.kind == DiagnosticKind::Syntax }));
    let Item::Definition(definition) = &outcome.ast.items[0] else {
        panic!("definition");
    };
    let Statement::If { then_branch, .. } = &definition.body.statements[0] else {
        panic!("conditional");
    };
    let Statement::Block(block) = then_branch.as_ref() else {
        panic!("nested block");
    };
    let Statement::Error { .. } = &block.statements[0] else {
        panic!("nested error");
    };
    let Statement::Declaration(_) = &block.statements[1] else {
        panic!("nested declaration");
    };
    let Statement::Return { .. } = &definition.body.statements[1] else {
        panic!("outer return");
    };
    assert_spans(source, &outcome);
}

#[test]
fn malformed_final_statement_recovers_at_enclosing_brace() {
    let source = "function F() { var a = } function G() { return 2; }";
    let outcome = parse(source);
    assert!(outcome
        .diagnostics
        .iter()
        .any(|diagnostic| { diagnostic.kind == DiagnosticKind::Syntax }));
    let Item::Definition(first) = &outcome.ast.items[0] else {
        panic!("first definition");
    };
    assert_eq!(first.name.name, "F");
    let Statement::Error { .. } = &first.body.statements[0] else {
        panic!("error statement");
    };
    assert!(has_definition(&outcome, "G"));

    let nested = "function F() { if (1) { var a = } return 3; } function G() { return 2; }";
    let outcome = parse(nested);
    assert!(outcome
        .diagnostics
        .iter()
        .any(|diagnostic| { diagnostic.kind == DiagnosticKind::Syntax }));
    let Item::Definition(first) = &outcome.ast.items[0] else {
        panic!("first definition");
    };
    let Statement::If { then_branch, .. } = &first.body.statements[0] else {
        panic!("conditional");
    };
    let Statement::Block(block) = then_branch.as_ref() else {
        panic!("nested block");
    };
    let Statement::Error { .. } = &block.statements[0] else {
        panic!("nested error");
    };
    let Statement::Return { .. } = &first.body.statements[1] else {
        panic!("outer return");
    };
    assert!(has_definition(&outcome, "G"));
    assert_spans(nested, &outcome);
}

#[test]
fn repeated_malformed_statements_each_emit_diagnostics() {
    let source = "function F() { var a = ; var b = ; return 3; }";
    let outcome = parse(source);
    let errors = outcome
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.kind == DiagnosticKind::Syntax)
        .count();
    assert!(errors >= 2, "{:?}", outcome.diagnostics);
    let Item::Definition(first) = &outcome.ast.items[0] else {
        panic!("definition");
    };
    let Statement::Error { .. } = &first.body.statements[0] else {
        panic!("first error");
    };
    let Statement::Error { .. } = &first.body.statements[1] else {
        panic!("second error");
    };
    let Statement::Return { .. } = &first.body.statements[2] else {
        panic!("later return");
    };
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
fn nested_call_and_tuple_children_retain_order_and_spans() {
    let source = "function F(){return A(B(1,(2,3)),C([4,5],D(6)),7);}";
    let outcome = parse(source);
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    let mut names = Vec::new();
    let mut numbers = Vec::new();
    outcome.ast.walk_syntax(None, &mut |kind, span, _| {
        let text = &source[span.start()..span.end()];
        if kind == SyntaxCategory::Identifier {
            names.push(text);
        }
        if kind == SyntaxCategory::Expression {
            if let Ok(number) = text.parse::<u8>() {
                numbers.push(number);
            }
        }
    });
    assert_eq!(names, ["F", "A", "B", "C", "D"]);
    assert_eq!(numbers, [1, 2, 3, 4, 5, 6, 7]);
    assert_spans(source, &outcome);
}

#[test]
fn invalid_expression_statement_preserves_later_call_and_neighbor() {
    for invalid in ["1;", "1 + 2;", "Rejected();"] {
        let source = format!(
            "function F() {{ {invalid} return Missing(); }} function Neighbor() {{ return 0; }}"
        );
        let outcome = parse(&source);
        let Item::Definition(first) = &outcome.ast.items[0] else {
            panic!("invalid statement must preserve F: {:?}", outcome.ast.items);
        };
        assert_eq!(first.name.name, "F");
        assert_eq!(first.body.statements.len(), 2);
        let Statement::Error { span } = first.body.statements[0] else {
            panic!("invalid expression must become an error statement");
        };
        assert_eq!(&source[span.start()..span.end()], invalid);
        assert_eq!(outcome.diagnostics.len(), 1, "{:?}", outcome.diagnostics);
        let diagnostic = &outcome.diagnostics[0];
        assert_eq!(diagnostic.kind, DiagnosticKind::Syntax);
        assert_eq!(diagnostic.span(), Some(span));
        assert_eq!(
            diagnostic.message,
            "only an anonymous component call may be used as an expression statement"
        );
        assert_missing_return(&first.body.statements[1]);
        assert!(has_definition(&outcome, "Neighbor"));
        assert_spans(&source, &outcome);
    }
}

#[test]
fn repeated_invalid_expression_statements_have_one_diagnostic_each() {
    let source = "function F() { 1; Rejected(); return Missing(); }";
    let outcome = parse(source);
    let Item::Definition(first) = &outcome.ast.items[0] else {
        panic!("invalid statements must preserve F");
    };
    assert_eq!(first.body.statements.len(), 3);
    assert_eq!(outcome.diagnostics.len(), 2, "{:?}", outcome.diagnostics);
    for (index, expected) in ["1;", "Rejected();"].iter().enumerate() {
        let Statement::Error { span } = first.body.statements[index] else {
            panic!("invalid expression must become an error statement");
        };
        assert_eq!(&source[span.start()..span.end()], *expected);
        assert_eq!(outcome.diagnostics[index].span(), Some(span));
        assert_eq!(outcome.diagnostics[index].kind, DiagnosticKind::Syntax);
    }
    assert_missing_return(&first.body.statements[2]);
    assert_spans(source, &outcome);
}

#[test]
fn invalid_expression_statement_preserves_enclosing_control_flow() {
    let source = "function F() { { 1; } if (1) 2; while (1) 3; \
                  for (var i = 0; i < 1; i++) 4; return Missing(); }";
    let outcome = parse(source);
    let Item::Definition(first) = &outcome.ast.items[0] else {
        panic!("nested invalid statements must preserve F");
    };
    assert_eq!(first.body.statements.len(), 5);
    assert_eq!(outcome.diagnostics.len(), 4, "{:?}", outcome.diagnostics);
    let Statement::Block(block) = &first.body.statements[0] else {
        panic!("nested block must survive");
    };
    let Statement::If { then_branch, .. } = &first.body.statements[1] else {
        panic!("conditional must survive");
    };
    let Statement::While { body: while_body, .. } = &first.body.statements[2] else {
        panic!("while loop must survive");
    };
    let Statement::For { body: for_body, .. } = &first.body.statements[3] else {
        panic!("for loop must survive");
    };
    let nested = [&block.statements[0], then_branch.as_ref(), while_body.as_ref(), for_body];
    for (index, (statement, expected)) in
        nested.into_iter().zip(["1;", "2;", "3;", "4;"]).enumerate()
    {
        let Statement::Error { span } = statement else {
            panic!("nested invalid expression must become an error statement");
        };
        assert_eq!(&source[span.start()..span.end()], expected);
        assert_eq!(outcome.diagnostics[index].kind, DiagnosticKind::Syntax);
        assert_eq!(outcome.diagnostics[index].span(), Some(*span));
    }
    assert_missing_return(&first.body.statements[4]);
    assert_spans(source, &outcome);
}

#[test]
fn valid_anonymous_expression_statement_remains_a_call() {
    let source = "template Main() { Sink()(1); }";
    let outcome = parse(source);
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    let Item::Definition(definition) = &outcome.ast.items[0] else {
        panic!("template must survive");
    };
    let Statement::AnonymousCall { call, span } = &definition.body.statements[0] else {
        panic!("valid anonymous expression statement must remain a call");
    };
    assert_eq!(call.name.name, "Sink");
    assert_eq!(&source[span.start()..span.end()], "Sink()(1);");
    assert_spans(source, &outcome);
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
fn custom_templates_pragma_enforces_its_declared_minimum() {
    let old = parse("pragma circom 2.0.5; pragma custom_templates;");
    assert!(old
        .diagnostics
        .iter()
        .any(|diagnostic| { diagnostic.kind == DiagnosticKind::FeatureVersion }));
    let supported = parse("pragma circom 2.0.6; pragma custom_templates;");
    assert!(supported.diagnostics.is_empty(), "{:?}", supported.diagnostics);
}

#[test]
fn reverse_assignment_keeps_the_assigned_variable_as_target() {
    let source = "template T() { var a; var b; a --> b; a ==> b; }";
    let outcome = parse(source);
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    let Item::Definition(definition) = &outcome.ast.items[0] else {
        panic!("definition");
    };
    for statement in &definition.body.statements[2..] {
        let Statement::Assignment { target, value, .. } = statement else {
            panic!("reverse assignment");
        };
        let Expression::Name { identifier: target, .. } = target else {
            panic!("target");
        };
        let Expression::Name { identifier: value, .. } = value else {
            panic!("value");
        };
        assert_eq!(target.name, "b");
        assert_eq!(value.name, "a");
    }
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
    assert_eq!(*operator, circomspect_parser::frontend::BinaryOperator::Add);
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
    assert_eq!(project.policy, VersionPolicy::new(Version::new(2, 2, 3)));
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
    use circomspect_parser::frontend::{DeclarationKind, DirectionSyntax};

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

#[test]
fn unsupported_major_and_future_pragma_versions_have_source_locations() {
    for pragma in ["1.0.0", "2.3.0"] {
        let source = format!("pragma circom {pragma}; template Valid(){{}}");
        let outcome = parse(&source);
        let diagnostic = outcome
            .diagnostics
            .iter()
            .find(|item| item.kind == DiagnosticKind::UnsupportedVersion)
            .unwrap();
        assert_eq!(diagnostic.span().unwrap().start(), 0);
        assert!(has_definition(&outcome, "Valid"));
    }
}
