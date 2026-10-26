//! Owned Circom source frontend with recovery at definition and statement boundaries.

mod source;
mod lexer;
mod loader;
mod parsed;
mod ast;
mod walk;

// LALRPOP emits its own parser machine, including unreachable-state panics and
// generated patterns. These exceptions apply only to generated code; the grammar,
// lexer, recovery, and lifting code retain the workspace policy. Rust 1.74 cannot
// use `expect` lint attributes yet.
lalrpop_mod!(
    #[allow(
        clippy::all,
        clippy::pedantic,
        clippy::allow_attributes,
        clippy::unwrap_used,
        clippy::panic
    )]
    syntax,
    "/frontend/syntax.rs"
);

pub use crate::frontend::source::{
    DiagnosticKind, DiagnosticLocation, SourceId, Span, SyntaxDiagnostic, Version, VersionPolicy,
};
pub use crate::frontend::lexer::{tokenize, LexOutcome, Token, TokenKind, Trivia, TriviaKind};
pub use crate::frontend::loader::{load_sources, LoadedProject, SourceFile};
pub use crate::frontend::ast::{
    Access, AnonymousCallExpr, AnonymousInput, ArgumentList, AssignmentOperator, BinaryOperator,
    Block, Declaration, DeclarationKind, DeclaredSymbol, Definition, DefinitionKind,
    DirectionSyntax, Expression, Identifier, InputAssignmentOperator, Item, LogArgument,
    ParseOutcome, PendingFeatureCheck, PendingFeatureKind, PortDirection, PostfixOperator, Pragma,
    SourceAst, SpannedDirection, Statement, SymbolSyntax, UnaryOperator,
};
pub use crate::frontend::walk::{SyntaxCategory, WalkSyntax};

use crate::frontend::parsed::{finish_segments, ParseContext, ParsedSegment};

use lalrpop_util::ParseError;

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

fn syntax_error_message(error: &ParseError<usize, TokenKind, ()>) -> &'static str {
    match error {
        ParseError::InvalidToken { .. } => "invalid token in Circom source",
        ParseError::UnrecognizedEof { .. } => "unexpected end of Circom source",
        ParseError::UnrecognizedToken { .. } => "unexpected token in Circom source",
        ParseError::ExtraToken { .. } => "unexpected trailing token in Circom source",
        ParseError::User { .. } => "invalid Circom syntax",
    }
}

fn parse_segment(source: SourceId, segment: &[Token]) -> Result<ParsedSegment, SyntaxDiagnostic> {
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
    let mut context = ParseContext::new(source);
    syntax::ItemParser::new().parse(&mut context, tokens).map(|item| context.finish(item)).map_err(
        |error| {
            let (start, finish) = parse_error_location(&error, end);
            SyntaxDiagnostic::new(
                DiagnosticKind::Syntax,
                Span::from_lexer(source, start, finish),
                syntax_error_message(&error),
            )
        },
    )
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
                items.push(ParsedSegment::error(
                    source,
                    Span::from_lexer(source, first.span.start(), last.span.end()),
                ));
            }
        }
        cursor = end;
    }
    let (items, pending_feature_checks) = finish_segments(items, policy, &mut lexed.diagnostics);
    let ast = SourceAst { source, items, trivia: lexed.trivia };
    ParseOutcome { ast, diagnostics: lexed.diagnostics, pending_feature_checks }
}
