use crate::frontend::source::{DiagnosticKind, SourceId, Span, SyntaxDiagnostic};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TokenKind {
    Ident(String),
    Number(String),
    String(String),
    Invalid(String),
    Pragma,
    Circom,
    CustomTemplates,
    Include,
    Function,
    Template,
    Bus,
    Custom,
    ExternC,
    Parallel,
    Component,
    Main,
    Public,
    Signal,
    Input,
    Output,
    Var,
    If,
    Else,
    For,
    While,
    Return,
    Assert,
    Log,
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Semicolon,
    Comma,
    Dot,
    Question,
    Colon,
    Assign,
    LeftSignal,
    LeftConstraint,
    RightSignal,
    RightConstraint,
    EqConstraint,
    AddAssign,
    SubAssign,
    MulAssign,
    DivAssign,
    IntDivAssign,
    ModAssign,
    PowAssign,
    ShlAssign,
    ShrAssign,
    AndAssign,
    OrAssign,
    XorAssign,
    Increment,
    Decrement,
    BoolOr,
    BoolAnd,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    BitOr,
    BitXor,
    BitAnd,
    Shl,
    Shr,
    Plus,
    Minus,
    Star,
    Slash,
    Backslash,
    Percent,
    Pow,
    Not,
    Complement,
    Underscore,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

pub struct LexOutcome {
    pub tokens: Vec<Token>,
    pub diagnostics: Vec<SyntaxDiagnostic>,
    pub trivia: Vec<Trivia>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TriviaKind {
    LineComment,
    BlockComment,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Trivia {
    pub kind: TriviaKind,
    pub span: Span,
}

fn keyword(word: &str) -> Option<TokenKind> {
    Some(match word {
        "pragma" => TokenKind::Pragma,
        "circom" => TokenKind::Circom,
        "custom_templates" => TokenKind::CustomTemplates,
        "include" => TokenKind::Include,
        "function" => TokenKind::Function,
        "template" => TokenKind::Template,
        "bus" => TokenKind::Bus,
        "custom" => TokenKind::Custom,
        "extern_c" => TokenKind::ExternC,
        "parallel" => TokenKind::Parallel,
        "component" => TokenKind::Component,
        "main" => TokenKind::Main,
        "public" => TokenKind::Public,
        "signal" => TokenKind::Signal,
        "input" => TokenKind::Input,
        "output" => TokenKind::Output,
        "var" => TokenKind::Var,
        "if" => TokenKind::If,
        "else" => TokenKind::Else,
        "for" => TokenKind::For,
        "while" => TokenKind::While,
        "return" => TokenKind::Return,
        "assert" => TokenKind::Assert,
        "log" => TokenKind::Log,
        "_" => TokenKind::Underscore,
        _ => return None,
    })
}

fn punctuation(rest: &str) -> Option<(TokenKind, usize)> {
    const TABLE: &[(&str, TokenKind)] = &[
        ("<==", TokenKind::LeftConstraint),
        ("==>", TokenKind::RightConstraint),
        ("<--", TokenKind::LeftSignal),
        ("-->", TokenKind::RightSignal),
        ("===", TokenKind::EqConstraint),
        ("<<=", TokenKind::ShlAssign),
        (">>=", TokenKind::ShrAssign),
        ("**=", TokenKind::PowAssign),
        ("\\=", TokenKind::IntDivAssign),
        ("+=", TokenKind::AddAssign),
        ("-=", TokenKind::SubAssign),
        ("*=", TokenKind::MulAssign),
        ("/=", TokenKind::DivAssign),
        ("%=", TokenKind::ModAssign),
        ("&=", TokenKind::AndAssign),
        ("|=", TokenKind::OrAssign),
        ("^=", TokenKind::XorAssign),
        ("++", TokenKind::Increment),
        ("--", TokenKind::Decrement),
        ("||", TokenKind::BoolOr),
        ("&&", TokenKind::BoolAnd),
        ("==", TokenKind::Eq),
        ("!=", TokenKind::Ne),
        ("<=", TokenKind::Le),
        (">=", TokenKind::Ge),
        ("<<", TokenKind::Shl),
        (">>", TokenKind::Shr),
        ("**", TokenKind::Pow),
        ("{", TokenKind::LBrace),
        ("}", TokenKind::RBrace),
        ("(", TokenKind::LParen),
        (")", TokenKind::RParen),
        ("[", TokenKind::LBracket),
        ("]", TokenKind::RBracket),
        (";", TokenKind::Semicolon),
        (",", TokenKind::Comma),
        (".", TokenKind::Dot),
        ("?", TokenKind::Question),
        (":", TokenKind::Colon),
        ("=", TokenKind::Assign),
        ("<", TokenKind::Lt),
        (">", TokenKind::Gt),
        ("|", TokenKind::BitOr),
        ("^", TokenKind::BitXor),
        ("&", TokenKind::BitAnd),
        ("+", TokenKind::Plus),
        ("-", TokenKind::Minus),
        ("*", TokenKind::Star),
        ("/", TokenKind::Slash),
        ("\\", TokenKind::Backslash),
        ("%", TokenKind::Percent),
        ("!", TokenKind::Not),
        ("~", TokenKind::Complement),
    ];
    for (spelling, kind) in TABLE {
        if rest.starts_with(spelling) {
            return Some((kind.clone(), spelling.len()));
        }
    }
    None
}

fn ascii_ident_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || byte == b'_' || byte == b'$'
}

fn ascii_ident_continue(byte: u8) -> bool {
    ascii_ident_start(byte) || byte.is_ascii_digit()
}

fn valid_identifier(word: &str) -> bool {
    let prefix = word.bytes().take_while(|byte| *byte == b'_' || *byte == b'$').count();
    word.as_bytes().get(prefix).is_some_and(u8::is_ascii_alphabetic)
}

struct Scanned {
    kind: TokenKind,
    end: usize,
    diagnostic: Option<SyntaxDiagnostic>,
}

fn scan_string(source: SourceId, text: &str, start: usize) -> Scanned {
    let rest = &text[start..];
    let after_quote = &rest[1..];
    let end = after_quote.find(['"', '\n']);
    if let Some(offset) = end {
        if after_quote.as_bytes()[offset] == b'"' {
            return Scanned {
                kind: TokenKind::String(after_quote[..offset].to_owned()),
                end: start + offset + 2,
                diagnostic: None,
            };
        }
    }
    let end = start + end.map_or(rest.len(), |offset| offset + 1);
    Scanned {
        kind: TokenKind::Invalid(text[start..end].to_owned()),
        end,
        diagnostic: Some(SyntaxDiagnostic::new(
            DiagnosticKind::UnterminatedString,
            Span::from_lexer(source, start, end),
            "unterminated string literal",
        )),
    }
}

fn scan_number(source: SourceId, text: &str, start: usize) -> Scanned {
    let bytes = text.as_bytes();
    let hexadecimal = text[start..].starts_with("0x");
    let mut end = start + if hexadecimal { 2 } else { 1 };
    while end < bytes.len()
        && if hexadecimal { bytes[end].is_ascii_hexdigit() } else { bytes[end].is_ascii_digit() }
    {
        end += 1;
    }
    if hexadecimal && end == start + 2 {
        return Scanned {
            kind: TokenKind::Invalid(text[start..end].to_owned()),
            end,
            diagnostic: Some(SyntaxDiagnostic::new(
                DiagnosticKind::InvalidNumber,
                Span::from_lexer(source, start, end),
                "hexadecimal literal requires a digit",
            )),
        };
    }
    Scanned { kind: TokenKind::Number(text[start..end].to_owned()), end, diagnostic: None }
}

fn scan_identifier(source: SourceId, text: &str, start: usize) -> Scanned {
    let bytes = text.as_bytes();
    let mut end = start + 1;
    while end < bytes.len() && ascii_ident_continue(bytes[end]) {
        end += 1;
    }
    let word = &text[start..end];
    if word != "_" && !valid_identifier(word) {
        return Scanned {
            kind: TokenKind::Invalid(word.to_owned()),
            end,
            diagnostic: Some(SyntaxDiagnostic::new(
                DiagnosticKind::InvalidToken,
                Span::from_lexer(source, start, end),
                "identifier must contain an ASCII letter",
            )),
        };
    }
    Scanned {
        kind: keyword(word).unwrap_or_else(|| TokenKind::Ident(word.to_owned())),
        end,
        diagnostic: None,
    }
}

fn scan_token(source: SourceId, text: &str, start: usize) -> Scanned {
    let rest = &text[start..];
    let first = text.as_bytes()[start];
    if first == b'"' {
        return scan_string(source, text, start);
    }
    if first.is_ascii_digit() {
        return scan_number(source, text, start);
    }
    if ascii_ident_start(first) {
        return scan_identifier(source, text, start);
    }
    if let Some((kind, len)) = punctuation(rest) {
        return Scanned { kind, end: start + len, diagnostic: None };
    }
    let end = start + rest.chars().next().map_or(1, char::len_utf8);
    Scanned {
        kind: TokenKind::Invalid(text[start..end].to_owned()),
        end,
        diagnostic: Some(SyntaxDiagnostic::new(
            DiagnosticKind::InvalidToken,
            Span::from_lexer(source, start, end),
            "invalid Circom token",
        )),
    }
}

/// Converts UTF-8 source into authored Circom tokens with byte-accurate spans.
#[must_use]
pub fn tokenize(source: SourceId, text: &str) -> LexOutcome {
    let mut index = 0;
    let mut tokens = Vec::new();
    let mut diagnostics = Vec::new();
    let mut trivia = Vec::new();
    while index < text.len() {
        let rest = &text[index..];
        if let Some(character) = rest.chars().next().filter(|character| character.is_whitespace()) {
            index += character.len_utf8();
            continue;
        }
        if rest.starts_with("//") {
            let start = index;
            index += rest.find('\n').unwrap_or(rest.len());
            trivia.push(Trivia {
                kind: TriviaKind::LineComment,
                span: Span::from_lexer(source, start, index),
            });
            continue;
        }
        if let Some(body) = rest.strip_prefix("/*") {
            if let Some(end) = body.find("*/") {
                let start = index;
                index += end + 4;
                trivia.push(Trivia {
                    kind: TriviaKind::BlockComment,
                    span: Span::from_lexer(source, start, index),
                });
            } else {
                diagnostics.push(SyntaxDiagnostic::new(
                    DiagnosticKind::UnterminatedComment,
                    Span::from_lexer(source, index, text.len()),
                    "unterminated block comment",
                ));
                tokens.push(Token {
                    kind: TokenKind::Invalid(rest.to_owned()),
                    span: Span::from_lexer(source, index, text.len()),
                });
                break;
            }
            continue;
        }
        let scanned = scan_token(source, text, index);
        if let Some(diagnostic) = scanned.diagnostic {
            diagnostics.push(diagnostic);
        }
        tokens
            .push(Token { kind: scanned.kind, span: Span::from_lexer(source, index, scanned.end) });
        index = scanned.end;
    }
    LexOutcome { tokens, diagnostics, trivia }
}
