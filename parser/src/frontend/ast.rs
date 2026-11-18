use crate::frontend::source::{SourceId, Span, SyntaxDiagnostic, Version};
use crate::frontend::lexer::Trivia;

/// A parsed file whose public nodes have structurally valid, named fields.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceAst {
    pub source: SourceId,
    pub items: Vec<Item>,
    pub trivia: Vec<Trivia>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseOutcome {
    pub ast: SourceAst,
    pub diagnostics: Vec<SyntaxDiagnostic>,
    pub pending_feature_checks: Vec<PendingFeatureCheck>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PendingFeatureKind {
    InlineArrayElementType,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct PendingFeatureCheck {
    pub kind: PendingFeatureKind,
    pub span: Span,
    pub required_version: Version,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Item {
    Pragma { pragma: Pragma, span: Span },
    Include { path: String, span: Span },
    Definition(Definition),
    Main { public: Vec<Identifier>, instance: Expression, span: Span },
    Error { span: Span },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Pragma {
    Version(Version),
    CustomTemplates,
}

impl Item {
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            Self::Pragma { span, .. }
            | Self::Include { span, .. }
            | Self::Main { span, .. }
            | Self::Error { span } => *span,
            Self::Definition(definition) => definition.span,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Identifier {
    pub name: String,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DefinitionKind {
    Function,
    Template { custom: bool, external: bool, parallel: bool },
    Bus,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Definition {
    pub kind: DefinitionKind,
    pub name: Identifier,
    pub parameters: ArgumentList<Identifier>,
    pub body: Block,
    pub span: Span,
}

/// Records whether optional parentheses were written in the source.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ArgumentList<T> {
    Omitted,
    Parenthesized(Vec<T>),
}

impl<T> ArgumentList<T> {
    #[must_use]
    pub fn values(&self) -> &[T] {
        match self {
            Self::Omitted => &[],
            Self::Parenthesized(values) => values,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block {
    pub statements: Vec<Statement>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Statement {
    Block(Block),
    Declaration(Declaration),
    /// `target` is the assigned lvalue for every operator, including reverse spellings.
    Assignment {
        target: Expression,
        operator: AssignmentOperator,
        value: Expression,
        span: Span,
    },
    PostfixUpdate {
        target: Expression,
        operator: PostfixOperator,
        span: Span,
    },
    Constraint {
        left: Expression,
        right: Expression,
        span: Span,
    },
    If {
        condition: Expression,
        then_branch: Box<Self>,
        else_branch: Option<Box<Self>>,
        span: Span,
    },
    For {
        initializer: Box<Self>,
        condition: Expression,
        step: Box<Self>,
        body: Box<Self>,
        span: Span,
    },
    While {
        condition: Expression,
        body: Box<Self>,
        span: Span,
    },
    Return {
        value: Expression,
        span: Span,
    },
    Assert {
        condition: Expression,
        span: Span,
    },
    Log {
        arguments: Vec<LogArgument>,
        span: Span,
    },
    AnonymousCall {
        call: AnonymousCallExpr,
        span: Span,
    },
    Error {
        span: Span,
    },
}

impl Statement {
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            Self::Block(block) => block.span,
            Self::Declaration(declaration) => declaration.span,
            Self::Assignment { span, .. }
            | Self::PostfixUpdate { span, .. }
            | Self::Constraint { span, .. }
            | Self::If { span, .. }
            | Self::For { span, .. }
            | Self::While { span, .. }
            | Self::Return { span, .. }
            | Self::Assert { span, .. }
            | Self::Log { span, .. }
            | Self::AnonymousCall { span, .. }
            | Self::Error { span } => *span,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LogArgument {
    String { value: String, span: Span },
    Expression(Expression),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Declaration {
    pub kind: DeclarationKind,
    pub symbol_syntax: SymbolSyntax,
    pub symbols: Vec<DeclaredSymbol>,
    pub tuple_initialization: Option<(AssignmentOperator, Expression)>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SymbolSyntax {
    List,
    Tuple,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PortDirection {
    Input,
    Output,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum DirectionSyntax {
    Unspecified,
    Before(SpannedDirection),
    After(SpannedDirection),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SpannedDirection {
    pub direction: PortDirection,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DeclarationKind {
    Variable,
    Component,
    Signal {
        direction: DirectionSyntax,
        tags: Vec<Identifier>,
    },
    Bus {
        type_name: Identifier,
        arguments: ArgumentList<Expression>,
        direction: DirectionSyntax,
        tags: Vec<Identifier>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclaredSymbol {
    pub name: Identifier,
    pub dimensions: Vec<Expression>,
    pub initialization: Option<(AssignmentOperator, Expression)>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Access {
    Field { field: Identifier, span: Span },
    Index { expression: Box<Expression>, span: Span },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AnonymousInput {
    Positional(Expression),
    Named { name: Identifier, operator: InputAssignmentOperator, value: Expression, span: Span },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AnonymousCallExpr {
    pub name: Identifier,
    pub parameters: Vec<Expression>,
    pub inputs: Vec<AnonymousInput>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expression {
    Name { identifier: Identifier, access: Vec<Access>, span: Span },
    Number { text: String, span: Span },
    Call { name: Identifier, arguments: Vec<Self>, span: Span },
    AnonymousCall(AnonymousCallExpr),
    Array { elements: Vec<Self>, span: Span },
    Tuple { elements: Vec<Self>, span: Span },
    Unary { operator: UnaryOperator, operand: Box<Self>, span: Span },
    Binary { operator: BinaryOperator, left: Box<Self>, right: Box<Self>, span: Span },
    Ternary { condition: Box<Self>, yes: Box<Self>, no: Box<Self>, span: Span },
    Parallel { operand: Box<Self>, span: Span },
    Group { expression: Box<Self>, span: Span },
    Error { span: Span },
}

impl Expression {
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            Self::Name { span, .. }
            | Self::Number { span, .. }
            | Self::Call { span, .. }
            | Self::Array { span, .. }
            | Self::Tuple { span, .. }
            | Self::Unary { span, .. }
            | Self::Binary { span, .. }
            | Self::Ternary { span, .. }
            | Self::Parallel { span, .. }
            | Self::Group { span, .. }
            | Self::Error { span } => *span,
            Self::AnonymousCall(call) => call.span,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnaryOperator {
    BooleanNot,
    Complement,
    Negate,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BinaryOperator {
    BooleanOr,
    BooleanAnd,
    Equal,
    NotEqual,
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    BitOr,
    BitXor,
    BitAnd,
    ShiftLeft,
    ShiftRight,
    Add,
    Subtract,
    Multiply,
    Divide,
    IntegerDivide,
    Modulo,
    Power,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssignmentOperator {
    Assign,
    Witness,
    Constraint,
    ReverseWitness,
    ReverseConstraint,
    Add,
    Subtract,
    Multiply,
    Divide,
    IntegerDivide,
    Modulo,
    Power,
    ShiftLeft,
    ShiftRight,
    BitAnd,
    BitOr,
    BitXor,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PostfixOperator {
    Increment,
    Decrement,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InputAssignmentOperator {
    Assign,
    Witness,
    Constraint,
}

impl InputAssignmentOperator {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Assign => "=",
            Self::Witness => "<--",
            Self::Constraint => "<==",
        }
    }
}
