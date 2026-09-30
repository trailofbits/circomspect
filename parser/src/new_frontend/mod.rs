//! Owned Circom source frontend. The legacy runtime remains separate until cutover.

mod ast;
mod lexer;
mod loader;
mod typed;
mod walk;

lalrpop_mod!(
    #[allow(clippy::all)]
    syntax,
    "/new_frontend/syntax.rs"
);

pub use ast::{
    DiagnosticKind, DiagnosticLocation, SourceId, Span, SyntaxDiagnostic, Version, VersionPolicy,
};
pub use lexer::{tokenize, LexOutcome, Token, TokenKind, Trivia, TriviaKind};
pub use loader::{load_sources, LoadedProject, SourceFile};
pub use typed::{
    Access, AnonymousCallExpr, AnonymousInput, ArgumentList, AssignmentOperator, BinaryOperator,
    Block, Declaration, DeclarationKind, DeclaredSymbol, Definition, DefinitionKind,
    DirectionSyntax, Expression, Identifier, InputAssignmentOperator, Item, LogArgument,
    ParseOutcome, PendingFeatureCheck, PendingFeatureKind, PortDirection, PostfixOperator, Pragma,
    SourceAst, SpannedDirection, Statement, UnaryOperator,
};
pub use walk::{SyntaxCategory, WalkSyntax};

use ast::{SyntaxKind, SyntaxNode};

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
    let Some(first) = segment.first() else {
        return Err(SyntaxDiagnostic::new(
            DiagnosticKind::Syntax,
            Span::from_lexer(source, 0, 0),
            "empty syntax segment",
        ));
    };
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

fn minimum_version(node: &SyntaxNode) -> Option<Version> {
    let release = match node.kind {
        SyntaxKind::Pragma if node.text.is_none() => (2, 0, 6),
        SyntaxKind::Modifier if node.text.as_deref() == Some("custom") => (2, 0, 6),
        SyntaxKind::Log => (2, 0, 7),
        SyntaxKind::Parallel => (2, 0, 8),
        SyntaxKind::Tags
        | SyntaxKind::Tuple
        | SyntaxKind::TupleDeclaration
        | SyntaxKind::AnonymousCall
        | SyntaxKind::Array => (2, 1, 0),
        SyntaxKind::Identifier if node.text.as_deref() == Some("_") => (2, 1, 0),
        SyntaxKind::Inputs if node.text.is_some() => (2, 1, 1),
        SyntaxKind::Bus
        | SyntaxKind::BusHeader
        | SyntaxKind::DirectionFirstBusHeader
        | SyntaxKind::DirectionFirstSignalHeader => (2, 2, 0),
        SyntaxKind::Modifier if node.text.as_deref() == Some("extern_c") => (2, 2, 3),
        _ => return None,
    };
    Some(Version::new(release.0, release.1, release.2))
}

fn contains_anonymous_call(node: &SyntaxNode) -> bool {
    node.kind == SyntaxKind::AnonymousCall || node.children.iter().any(contains_anonymous_call)
}

fn may_contain_bus(node: &SyntaxNode) -> bool {
    if node.kind == SyntaxKind::Name
        || node.kind == SyntaxKind::Call
        || node.kind == SyntaxKind::Group
        || node.kind == SyntaxKind::Array
        || node.kind == SyntaxKind::Tuple
        || node.kind == SyntaxKind::Ternary
    {
        return true;
    }
    node.children.iter().any(may_contain_bus)
}

fn validate_feature_node(
    node: &SyntaxNode,
    target: Version,
    declared: Option<Version>,
    diagnostics: &mut Vec<SyntaxDiagnostic>,
    pending: &mut Vec<PendingFeatureCheck>,
) {
    let anonymous_array =
        node.kind == SyntaxKind::Array && node.children.iter().any(contains_anonymous_call);
    let minimum = if anonymous_array { Some(Version::new(2, 2, 3)) } else { minimum_version(node) };
    if let Some(minimum) = minimum {
        let custom_pragma_too_old = node.kind == SyntaxKind::Modifier
            && node.text.as_deref() == Some("custom")
            && declared.is_some_and(|version| version < minimum);
        if target < minimum || custom_pragma_too_old {
            diagnostics.push(SyntaxDiagnostic::new(
                DiagnosticKind::FeatureVersion,
                node.span,
                format!(
                    "feature requires Circom {}.{}.{}",
                    minimum.major, minimum.minor, minimum.patch
                ),
            ));
        }
    }
    if node.kind == SyntaxKind::Array
        && target < Version::new(2, 2, 3)
        && !anonymous_array
        && node.children.iter().any(may_contain_bus)
    {
        pending.push(PendingFeatureCheck {
            kind: PendingFeatureKind::InlineArrayElementType,
            span: node.span,
            required_version: Version::new(2, 2, 3),
        });
    }
    for child in &node.children {
        validate_feature_node(child, target, declared, diagnostics, pending);
    }
}

fn validate_version(
    items: &[SyntaxNode],
    policy: VersionPolicy,
    diagnostics: &mut Vec<SyntaxDiagnostic>,
) -> Vec<PendingFeatureCheck> {
    let declared = items.iter().find_map(declared_version);
    for item in items {
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
            if let Some(pragma) = items.iter().find(|item| declared_version(item).is_some()) {
                diagnostics.push(SyntaxDiagnostic::new(
                    DiagnosticKind::UnsupportedVersion,
                    pragma.span,
                    "source requires a newer compiler than the selected target",
                ));
            }
        }
    }
    let mut pending = Vec::new();
    for item in items {
        validate_feature_node(item, policy.supported, declared, diagnostics, &mut pending);
    }
    pending
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
        let (Some(first), Some(last)) = (segment.first(), segment.last()) else {
            break;
        };
        match parse_segment(source, segment) {
            Ok(item) => items.push(item),
            Err(diagnostic) => {
                lexed.diagnostics.push(diagnostic);
                items.push(node(
                    SyntaxKind::Error,
                    source,
                    first.span.start(),
                    last.span.end(),
                    vec![],
                ));
            }
        }
        cursor = end;
    }
    let pending_feature_checks = validate_version(&items, policy, &mut lexed.diagnostics);
    validate_item_order(&items, &mut lexed.diagnostics);
    let mut typed_items = Vec::new();
    for item in items {
        let span = item.span;
        match typed::item(item) {
            Ok(item) => typed_items.push(item),
            Err(diagnostic) => {
                lexed.diagnostics.push(diagnostic);
                typed_items.push(Item::Error { span });
            }
        }
    }
    let ast = SourceAst { source, items: typed_items, trivia: lexed.trivia };
    ParseOutcome { ast, diagnostics: lexed.diagnostics, pending_feature_checks }
}
