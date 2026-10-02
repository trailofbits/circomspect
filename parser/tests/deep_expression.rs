use std::fs;

use circomspect_parser::hir::lift_project;
use circomspect_parser::new_frontend::{
    load_sources, parse_source, BinaryOperator, Expression, Item, SourceId, Statement, Version,
    VersionPolicy, WalkSyntax, SyntaxCategory,
};

fn source() -> String {
    let mut expression = String::new();
    for index in 0..254 {
        if index != 0 {
            expression.push('+');
        }
        expression.push_str(&format!("bits[{index}]*(2**{index})"));
    }
    format!("template T(){{signal input bits[254];signal output x;x<--{expression};}}")
}

#[test]
fn left_associated_254_term_expression_parses_on_the_default_stack() {
    let source = source();
    let parsed = parse_source(SourceId::new(0), &source, VersionPolicy::new(Version::new(2, 2, 3)));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let Some(Item::Definition(definition)) = parsed.ast.items.first() else {
        panic!("expected template definition");
    };
    let Some(Statement::Assignment { value, .. }) = definition.body.statements.last() else {
        panic!("expected witness assignment");
    };
    let mut current = value;
    let mut additions = 0;
    while let Expression::Binary { operator: BinaryOperator::Add, left, .. } = current {
        additions += 1;
        current = left;
    }
    assert_eq!(additions, 253);
    assert_eq!(&source[current.span().start()..current.span().end()], "bits[0]*(2**0)");
}

#[test]
fn left_associated_254_term_expression_lifts_on_the_default_stack() {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-deep-expression-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source()).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    assert!(lifted.hir.definition("T").is_some());
    assert!(lifted.hir.expressions().len() >= 254);
}

#[test]
fn independent_mixed_expression_frames_preserve_operand_order() {
    let source = "function F(){return K((1,2),[3,4],5?6:7,-(8+9));}";
    let parsed = parse_source(SourceId::new(0), source, VersionPolicy::new(Version::new(2, 2, 3)));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut values = Vec::new();
    parsed.ast.walk_syntax(None, &mut |kind, span, _| {
        if kind == SyntaxCategory::Expression {
            if let Ok(value) = source[span.start()..span.end()].parse::<u8>() {
                values.push(value);
            }
        }
    });
    assert_eq!(values, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
}

#[test]
fn independent_deep_syntax_walk_preserves_contained_source_spans() {
    let source = source();
    let parsed = parse_source(SourceId::new(0), &source, VersionPolicy::new(Version::new(2, 2, 3)));
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    parsed.ast.walk_syntax(None, &mut |_, span, parent| {
        assert!(source.is_char_boundary(span.start()));
        assert!(source.is_char_boundary(span.end()));
        assert!(span.start() <= span.end());
        assert!(span.end() <= source.len());
        if let Some(parent) = parent {
            assert_eq!(span.source(), parent.source());
            assert!(parent.start() <= span.start());
            assert!(span.end() <= parent.end());
        }
    });
}
