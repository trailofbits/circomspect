use crate::new_frontend::ast::{SourceId, Span, SyntaxKind, SyntaxNode};
use crate::new_frontend::typed::{expression, BinaryOperator};

fn syntax(kind: SyntaxKind, children: Vec<SyntaxNode>) -> SyntaxNode {
    SyntaxNode { kind, span: Span::from_lexer(SourceId::new(7), 0, 10), text: None, children }
}

fn identifier(name: &str) -> SyntaxNode {
    let mut node = syntax(SyntaxKind::Identifier, Vec::new());
    node.text = Some(name.to_owned());
    node
}

#[test]
fn expression_bridge_rejects_malformed_expressions() {
    let binary = syntax(SyntaxKind::Binary(BinaryOperator::Add), vec![identifier("a")]);
    for node in [syntax(SyntaxKind::Parameters, Vec::new()), binary] {
        assert!(expression(node).is_err());
    }
}

#[test]
fn expression_bridge_rejects_malformed_anonymous_calls() {
    for children in [
        vec![identifier("Sink")],
        vec![
            identifier("Sink"),
            syntax(SyntaxKind::Inputs, Vec::new()),
            syntax(SyntaxKind::Parameters, Vec::new()),
        ],
    ] {
        let call = syntax(SyntaxKind::AnonymousCall, children);
        assert!(expression(call).is_err());
    }
}
