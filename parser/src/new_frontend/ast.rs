use crate::new_frontend::typed::{BinaryOperator, InputAssignmentOperator, UnaryOperator};

use std::ops::Range;
use std::path::PathBuf;

/// Identifies one source file within a parsed project.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SourceId(usize);

impl SourceId {
    #[must_use]
    pub const fn new(value: usize) -> Self {
        Self(value)
    }

    #[must_use]
    pub const fn index(self) -> usize {
        self.0
    }
}

/// A byte range in a UTF-8 source file.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Span {
    source: SourceId,
    start: usize,
    end: usize,
}

impl Span {
    #[must_use]
    pub fn checked(source: SourceId, range: Range<usize>, text: &str) -> Option<Self> {
        if range.start <= range.end
            && range.end <= text.len()
            && text.is_char_boundary(range.start)
            && text.is_char_boundary(range.end)
        {
            Some(Self { source, start: range.start, end: range.end })
        } else {
            None
        }
    }

    pub(crate) const fn from_lexer(source: SourceId, start: usize, end: usize) -> Self {
        Self { source, start, end }
    }

    #[must_use]
    pub const fn source(self) -> SourceId {
        self.source
    }
    #[must_use]
    pub const fn start(self) -> usize {
        self.start
    }
    #[must_use]
    pub const fn end(self) -> usize {
        self.end
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SyntaxKind {
    Parameters,
    Inputs,
    NamedInput(InputAssignmentOperator),
    Name,
    Identifier,
    Number,
    Call,
    AnonymousCall,
    Access,
    Array,
    Tuple,
    Unary(UnaryOperator),
    Binary(BinaryOperator),
    Ternary,
    Parallel,
    Group,
}

/// A source-preserving syntax node; `text` stores names and literals.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxNode {
    pub kind: SyntaxKind,
    pub span: Span,
    pub text: Option<String>,
    pub children: Vec<Self>,
}

impl SyntaxNode {
    pub(crate) fn new(
        kind: SyntaxKind,
        source: SourceId,
        start: usize,
        end: usize,
        text: Option<String>,
        children: Vec<Self>,
    ) -> Self {
        Self { kind, span: Span::from_lexer(source, start, end), text, children }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Version {
    pub major: u32,
    pub minor: u32,
    pub patch: u32,
}

impl Version {
    #[must_use]
    pub const fn new(major: u32, minor: u32, patch: u32) -> Self {
        Self { major, minor, patch }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct VersionPolicy {
    pub supported: Version,
}

impl VersionPolicy {
    #[must_use]
    pub const fn new(supported: Version) -> Self {
        Self { supported }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DiagnosticKind {
    InvalidToken,
    UnterminatedString,
    UnterminatedComment,
    InvalidNumber,
    Syntax,
    UnsupportedVersion,
    FeatureVersion,
    MissingInclude,
    CyclicInclude,
    FileRead,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxDiagnostic {
    pub kind: DiagnosticKind,
    pub location: DiagnosticLocation,
    pub message: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DiagnosticLocation {
    Source(Span),
    Path(PathBuf),
}

impl SyntaxDiagnostic {
    pub(crate) fn new(kind: DiagnosticKind, span: Span, message: impl Into<String>) -> Self {
        Self { kind, location: DiagnosticLocation::Source(span), message: message.into() }
    }

    pub(crate) fn at_path(kind: DiagnosticKind, path: PathBuf, message: impl Into<String>) -> Self {
        Self { kind, location: DiagnosticLocation::Path(path), message: message.into() }
    }

    #[must_use]
    pub fn span(&self) -> Option<Span> {
        if let DiagnosticLocation::Source(span) = &self.location {
            Some(*span)
        } else {
            None
        }
    }
}
