use crate::new_frontend::ast::{
    DiagnosticKind, SourceId, Span, SyntaxDiagnostic, SyntaxKind, SyntaxNode,
};
use crate::new_frontend::typed::{item, statement, BinaryOperator};

fn syntax(kind: SyntaxKind, children: Vec<SyntaxNode>) -> SyntaxNode {
    SyntaxNode { kind, span: Span::from_lexer(SourceId::new(7), 0, 10), text: None, children }
}

fn identifier(name: &str) -> SyntaxNode {
    let mut node = syntax(SyntaxKind::Identifier, Vec::new());
    node.text = Some(name.to_owned());
    node
}

#[test]
fn expression_statement_requires_exactly_one_child() {
    for children in [Vec::new(), vec![identifier("a"), identifier("b")]] {
        let node = syntax(SyntaxKind::ExpressionStatement, children);
        let expected =
            SyntaxDiagnostic::new(DiagnosticKind::Syntax, node.span, "invalid syntax child count");
        assert_eq!(statement(node), Err(expected));
    }
}

#[test]
fn invalid_expression_statement_does_not_hide_malformed_expressions() {
    let binary = syntax(SyntaxKind::Binary(BinaryOperator::Add), vec![identifier("a")]);
    for expression in [syntax(SyntaxKind::Block, Vec::new()), binary] {
        let invalid = syntax(SyntaxKind::ExpressionStatement, vec![expression]);
        assert!(statement(invalid.clone()).is_err());
        let definition = syntax(
            SyntaxKind::Function,
            vec![identifier("F"), syntax(SyntaxKind::Block, vec![invalid])],
        );
        assert!(item(definition).is_err());
    }
}

#[test]
fn anonymous_expression_statement_does_not_hide_malformed_calls() {
    for children in [
        vec![identifier("Sink")],
        vec![
            identifier("Sink"),
            syntax(SyntaxKind::Inputs, Vec::new()),
            syntax(SyntaxKind::Parameters, Vec::new()),
        ],
    ] {
        let call = syntax(SyntaxKind::AnonymousCall, children);
        assert!(statement(syntax(SyntaxKind::ExpressionStatement, vec![call])).is_err());
    }
}
