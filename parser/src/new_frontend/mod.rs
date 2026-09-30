//! Owned Circom source frontend. The legacy runtime remains separate until cutover.

mod ast;
mod lexer;
mod loader;

lalrpop_mod!(
    #[allow(clippy::all)]
    syntax,
    "/new_frontend/syntax.rs"
);

pub use ast::{
    DiagnosticKind, ParseOutcome, SourceAst, SourceId, Span, SyntaxDiagnostic, SyntaxKind,
    SyntaxNode, Version, VersionPolicy,
};
pub use lexer::{tokenize, LexOutcome, Token, TokenKind};
pub use loader::{load_sources, LoadedProject, SourceFile};

use lalrpop_util::ParseError;

fn node(
    kind: SyntaxKind,
    source: SourceId,
    start: usize,
    end: usize,
    children: Vec<SyntaxNode>,
) -> SyntaxNode {
    SyntaxNode::new(kind, source, start, end, None, children)
}

fn labelled(
    kind: SyntaxKind,
    source: SourceId,
    start: usize,
    end: usize,
    label: String,
    children: Vec<SyntaxNode>,
) -> SyntaxNode {
    SyntaxNode::new(kind, source, start, end, Some(label), children)
}

fn starts_item(token: &TokenKind) -> bool {
    token == &TokenKind::Pragma
        || token == &TokenKind::Include
        || token == &TokenKind::Function
        || token == &TokenKind::Template
        || token == &TokenKind::Bus
        || token == &TokenKind::Component
}

fn starts_strong_boundary(token: &TokenKind) -> bool {
    token == &TokenKind::Pragma
        || token == &TokenKind::Include
        || token == &TokenKind::Function
        || token == &TokenKind::Template
        || token == &TokenKind::Bus
}

fn follows_closing_brace(token: &Token) -> bool {
    token.kind == TokenKind::RBrace
}

fn segment_end(tokens: &[Token], start: usize) -> usize {
    let definition = tokens[start].kind == TokenKind::Function
        || tokens[start].kind == TokenKind::Template
        || tokens[start].kind == TokenKind::Bus;
    let mut parens = 0_usize;
    let mut brackets = 0_usize;
    let mut braces = 0_usize;
    let mut saw_body = false;
    for index in start..tokens.len() {
        let kind = &tokens[index].kind;
        if index > start
            && (starts_strong_boundary(kind)
                || (starts_item(kind)
                    && braces == 0
                    && (parens == 0 || follows_closing_brace(&tokens[index - 1]))))
        {
            return index;
        }
        match kind {
            TokenKind::LParen => parens += 1,
            TokenKind::RParen => parens = parens.saturating_sub(1),
            TokenKind::LBracket => brackets += 1,
            TokenKind::RBracket => brackets = brackets.saturating_sub(1),
            TokenKind::LBrace => {
                braces += 1;
                saw_body = true;
            }
            TokenKind::RBrace => {
                braces = braces.saturating_sub(1);
                if definition && saw_body && braces == 0 {
                    return index + 1;
                }
            }
            TokenKind::Semicolon if !definition && parens == 0 && brackets == 0 && braces == 0 => {
                return index + 1
            }
            _ => {}
        }
    }
    tokens.len()
}

fn parse_error_location(
    error: &ParseError<usize, TokenKind, ()>,
    fallback: usize,
) -> (usize, usize) {
    match error {
        ParseError::InvalidToken { location } | ParseError::UnrecognizedEof { location, .. } => {
            (*location, *location)
        }
        ParseError::UnrecognizedToken { token, .. } | ParseError::ExtraToken { token } => {
            (token.0, token.2)
        }
        ParseError::User { .. } => (fallback, fallback),
    }
}

fn parse_segment(source: SourceId, segment: &[Token]) -> Result<SyntaxNode, SyntaxDiagnostic> {
    let Some(first) = segment.first() else { unreachable!("caller supplies nonempty segment") };
    let end = segment.last().map_or(first.span.end(), |token| token.span.end());
    let tokens =
        segment.iter().map(|token| Ok((token.span.start(), token.kind.clone(), token.span.end())));
    syntax::ItemParser::new().parse(source, tokens).map_err(|error| {
        let (start, finish) = parse_error_location(&error, end);
        SyntaxDiagnostic::new(
            DiagnosticKind::Syntax,
            Span::from_lexer(source, start, finish),
            format!("invalid Circom syntax: {error:?}"),
        )
    })
}

fn declared_version(item: &SyntaxNode) -> Option<Version> {
    if item.kind != SyntaxKind::Pragma {
        return None;
    }
    let text = item.text.as_ref()?;
    let mut parts = text.split('.');
    let major = parts.next()?.parse().ok()?;
    let minor = parts.next()?.parse().ok()?;
    let patch = parts.next()?.parse().ok()?;
    if parts.next().is_some() {
        return None;
    }
    Some(Version::new(major, minor, patch))
}

fn validate_version(
    ast: &SourceAst,
    tokens: &[Token],
    policy: VersionPolicy,
    diagnostics: &mut Vec<SyntaxDiagnostic>,
) {
    let declared = ast.items.iter().find_map(declared_version);
    for item in &ast.items {
        if item.kind == SyntaxKind::Pragma
            && item.text.is_some()
            && declared_version(item).is_none()
        {
            diagnostics.push(SyntaxDiagnostic::new(
                DiagnosticKind::InvalidNumber,
                item.span,
                "Circom version contains an out-of-range component",
            ));
        }
    }
    if let Some(version) = declared {
        if version > policy.supported {
            if let Some(pragma) = ast.items.iter().find(|item| declared_version(item).is_some()) {
                diagnostics.push(SyntaxDiagnostic::new(
                    DiagnosticKind::UnsupportedVersion,
                    pragma.span,
                    "source requests a newer Circom release than this frontend supports",
                ));
            }
        }
    }
    let effective = declared.unwrap_or(policy.supported);
    for token in tokens {
        let minimum = match token.kind {
            TokenKind::Bus | TokenKind::ExternC => Some(Version::new(2, 2, 0)),
            _ => None,
        };
        if let Some(minimum) = minimum {
            if effective < minimum || policy.supported < minimum {
                diagnostics.push(SyntaxDiagnostic::new(
                    DiagnosticKind::FeatureVersion,
                    token.span,
                    format!(
                        "feature requires Circom {}.{}.{}",
                        minimum.major, minimum.minor, minimum.patch
                    ),
                ));
            }
        }
    }
}

fn validate_node(node: &SyntaxNode, diagnostics: &mut Vec<SyntaxDiagnostic>) {
    if node.kind == SyntaxKind::ExpressionStatement {
        let valid =
            node.children.first().is_some_and(|child| child.kind == SyntaxKind::AnonymousCall);
        if !valid {
            diagnostics.push(SyntaxDiagnostic::new(
                DiagnosticKind::Syntax,
                node.span,
                "only an anonymous component call may be used as an expression statement",
            ));
        }
    }
    for child in &node.children {
        validate_node(child, diagnostics);
    }
}

fn validate_item_order(items: &[SyntaxNode], diagnostics: &mut Vec<SyntaxDiagnostic>) {
    let mut stage = 0_u8;
    for item in items {
        let expected = match item.kind {
            SyntaxKind::Pragma => 0,
            SyntaxKind::Include => 1,
            SyntaxKind::Main => 3,
            SyntaxKind::Error => continue,
            _ => 2,
        };
        if expected < stage || (expected == 3 && stage == 3) {
            diagnostics.push(SyntaxDiagnostic::new(
                DiagnosticKind::Syntax,
                item.span,
                "pragma, include, definition, and main declarations are out of order",
            ));
        }
        stage = stage.max(expected);
        validate_node(item, diagnostics);
    }
}

/// Parses one source file while retaining independent definitions after errors.
#[must_use]
pub fn parse_source(source: SourceId, text: &str, policy: VersionPolicy) -> ParseOutcome {
    let mut lexed = tokenize(source, text);
    let mut items = Vec::new();
    let mut cursor = 0;
    while cursor < lexed.tokens.len() {
        let end = segment_end(&lexed.tokens, cursor);
        let segment = &lexed.tokens[cursor..end];
        match parse_segment(source, segment) {
            Ok(item) => items.push(item),
            Err(diagnostic) => {
                lexed.diagnostics.push(diagnostic);
                items.push(node(
                    SyntaxKind::Error,
                    source,
                    segment[0].span.start(),
                    segment[segment.len() - 1].span.end(),
                    vec![],
                ));
            }
        }
        cursor = end;
    }
    let ast = SourceAst { source, items };
    validate_version(&ast, &lexed.tokens, policy, &mut lexed.diagnostics);
    validate_item_order(&ast.items, &mut lexed.diagnostics);
    ParseOutcome { ast, diagnostics: lexed.diagnostics }
}
