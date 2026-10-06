use super::ast::{DiagnosticKind, SourceId, Span, SyntaxDiagnostic, SyntaxKind, SyntaxNode, Version};
use super::lexer::Trivia;

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

fn malformed(node: &SyntaxNode, message: &str) -> SyntaxDiagnostic {
    SyntaxDiagnostic::new(DiagnosticKind::Syntax, node.span, message)
}

fn required_text(node: &SyntaxNode) -> Result<String, SyntaxDiagnostic> {
    node.text.clone().ok_or_else(|| malformed(node, "missing syntax name or operator"))
}

fn one_child(mut node: SyntaxNode) -> Result<SyntaxNode, SyntaxDiagnostic> {
    if node.children.len() == 1 {
        Ok(node.children.remove(0))
    } else {
        Err(malformed(&node, "invalid syntax child count"))
    }
}

fn two_children(mut node: SyntaxNode) -> Result<(SyntaxNode, SyntaxNode), SyntaxDiagnostic> {
    if node.children.len() == 2 {
        let right = node.children.remove(1);
        let left = node.children.remove(0);
        Ok((left, right))
    } else {
        Err(malformed(&node, "invalid syntax child count"))
    }
}

fn identifier(mut node: SyntaxNode) -> Result<Identifier, SyntaxDiagnostic> {
    if node.kind != SyntaxKind::Identifier || !node.children.is_empty() {
        return Err(malformed(&node, "expected identifier"));
    }
    let name =
        node.text.take().ok_or_else(|| malformed(&node, "missing syntax name or operator"))?;
    Ok(Identifier { name, span: node.span })
}

fn identifiers(nodes: Vec<SyntaxNode>) -> Result<Vec<Identifier>, SyntaxDiagnostic> {
    nodes.into_iter().map(identifier).collect()
}

fn direction(node: &SyntaxNode) -> Result<SpannedDirection, SyntaxDiagnostic> {
    if node.kind != SyntaxKind::Direction {
        return Err(malformed(node, "expected signal direction"));
    }
    let direction = match node.text.as_deref() {
        Some("input") => PortDirection::Input,
        Some("output") => PortDirection::Output,
        _ => return Err(malformed(node, "invalid signal direction")),
    };
    Ok(SpannedDirection { direction, span: node.span })
}

fn operator(node: &SyntaxNode) -> Result<AssignmentOperator, SyntaxDiagnostic> {
    let value = match node.text.as_deref() {
        Some("=") => AssignmentOperator::Assign,
        Some("<--") => AssignmentOperator::Witness,
        Some("<==") => AssignmentOperator::Constraint,
        Some("-->") => AssignmentOperator::ReverseWitness,
        Some("==>") => AssignmentOperator::ReverseConstraint,
        Some("+=") => AssignmentOperator::Add,
        Some("-=") => AssignmentOperator::Subtract,
        Some("*=") => AssignmentOperator::Multiply,
        Some("/=") => AssignmentOperator::Divide,
        Some("\\=") => AssignmentOperator::IntegerDivide,
        Some("%=") => AssignmentOperator::Modulo,
        Some("**=") => AssignmentOperator::Power,
        Some("<<=") => AssignmentOperator::ShiftLeft,
        Some(">>=") => AssignmentOperator::ShiftRight,
        Some("&=") => AssignmentOperator::BitAnd,
        Some("|=") => AssignmentOperator::BitOr,
        Some("^=") => AssignmentOperator::BitXor,
        _ => return Err(malformed(node, "invalid assignment operator")),
    };
    Ok(value)
}

fn input_operator(node: &SyntaxNode) -> Result<InputAssignmentOperator, SyntaxDiagnostic> {
    match node.text.as_deref() {
        Some("=") => Ok(InputAssignmentOperator::Assign),
        Some("<--") => Ok(InputAssignmentOperator::Witness),
        Some("<==") => Ok(InputAssignmentOperator::Constraint),
        _ => Err(malformed(node, "invalid anonymous input assignment operator")),
    }
}

fn postfix_operator(node: &SyntaxNode) -> Result<PostfixOperator, SyntaxDiagnostic> {
    match node.text.as_deref() {
        Some("++") => Ok(PostfixOperator::Increment),
        Some("--") => Ok(PostfixOperator::Decrement),
        _ => Err(malformed(node, "invalid postfix operator")),
    }
}

fn leading_identifier(node: &mut SyntaxNode) -> Result<Identifier, SyntaxDiagnostic> {
    if node.children.is_empty() {
        return Err(malformed(node, "missing identifier"));
    }
    identifier(node.children.remove(0))
}

fn unary_operator(node: &SyntaxNode) -> Result<UnaryOperator, SyntaxDiagnostic> {
    match node.text.as_deref() {
        Some("!") => Ok(UnaryOperator::BooleanNot),
        Some("~") => Ok(UnaryOperator::Complement),
        Some("-") => Ok(UnaryOperator::Negate),
        _ => Err(malformed(node, "invalid unary operator")),
    }
}

fn binary_operator(node: &SyntaxNode) -> Result<BinaryOperator, SyntaxDiagnostic> {
    let value = match node.text.as_deref() {
        Some("||") => BinaryOperator::BooleanOr,
        Some("&&") => BinaryOperator::BooleanAnd,
        Some("==") => BinaryOperator::Equal,
        Some("!=") => BinaryOperator::NotEqual,
        Some("<") => BinaryOperator::Less,
        Some(">") => BinaryOperator::Greater,
        Some("<=") => BinaryOperator::LessEqual,
        Some(">=") => BinaryOperator::GreaterEqual,
        Some("|") => BinaryOperator::BitOr,
        Some("^") => BinaryOperator::BitXor,
        Some("&") => BinaryOperator::BitAnd,
        Some("<<") => BinaryOperator::ShiftLeft,
        Some(">>") => BinaryOperator::ShiftRight,
        Some("+") => BinaryOperator::Add,
        Some("-") => BinaryOperator::Subtract,
        Some("*") => BinaryOperator::Multiply,
        Some("/") => BinaryOperator::Divide,
        Some("\\") => BinaryOperator::IntegerDivide,
        Some("%") => BinaryOperator::Modulo,
        Some("**") => BinaryOperator::Power,
        _ => return Err(malformed(node, "invalid binary operator")),
    };
    Ok(value)
}

fn access(node: SyntaxNode) -> Result<Access, SyntaxDiagnostic> {
    if node.kind != SyntaxKind::Access {
        return Err(malformed(&node, "expected field or index access"));
    }
    if node.children.first().is_some_and(|child| child.kind == SyntaxKind::Identifier) {
        let span = node.span;
        return Ok(Access::Field { field: identifier(one_child(node)?)?, span });
    }
    let span = node.span;
    Ok(Access::Index { expression: Box::new(expression(one_child(node)?)?), span })
}

fn anonymous_input(node: SyntaxNode) -> Result<AnonymousInput, SyntaxDiagnostic> {
    if node.kind != SyntaxKind::Inputs || node.text.is_none() {
        return expression(node).map(AnonymousInput::Positional);
    }
    let span = node.span;
    let operator = input_operator(&node)?;
    let (name_node, value_node) = two_children(node)?;
    Ok(AnonymousInput::Named {
        name: identifier(name_node)?,
        operator,
        value: expression(value_node)?,
        span,
    })
}

fn anonymous_call(mut node: SyntaxNode) -> Result<AnonymousCallExpr, SyntaxDiagnostic> {
    if node.kind != SyntaxKind::AnonymousCall {
        return Err(malformed(&node, "expected anonymous component call"));
    }
    let span = node.span;
    let name = leading_identifier(&mut node)?;
    let (parameters, inputs) = two_children(node)?;
    if parameters.kind != SyntaxKind::Parameters || inputs.kind != SyntaxKind::Inputs {
        return Err(malformed(&parameters, "invalid anonymous call argument groups"));
    }
    Ok(AnonymousCallExpr {
        name,
        parameters: parameters.children.into_iter().map(expression).collect::<Result<_, _>>()?,
        inputs: inputs.children.into_iter().map(anonymous_input).collect::<Result<_, _>>()?,
        span,
    })
}

enum ExpressionFrame {
    Visit(SyntaxNode),
    Operator(OperatorFrame),
    Collection(CollectionFrame),
}

#[derive(Clone, Copy)]
enum OperatorFrame {
    Unary(UnaryOperator, Span),
    Binary(BinaryOperator, Span),
    Ternary(Span),
    Parallel(Span),
    Group(Span),
}

enum CollectionFrame {
    Call(Identifier, Span, usize),
    Array(Span, usize),
    Tuple(Span, usize),
}

fn expression(node: SyntaxNode) -> Result<Expression, SyntaxDiagnostic> {
    let span = node.span;
    let mut work = vec![ExpressionFrame::Visit(node)];
    let mut results = Vec::new();
    while let Some(frame) = work.pop() {
        match frame {
            ExpressionFrame::Visit(node) => schedule_expression(node, &mut work, &mut results)?,
            ExpressionFrame::Operator(operator) => {
                let expression = assemble_operator(operator, &mut results)?;
                results.push(expression);
            }
            ExpressionFrame::Collection(collection) => {
                let expression = assemble_collection(collection, &mut results)?;
                results.push(expression);
            }
        }
    }
    let result = take_expression(&mut results, span)?;
    if !results.is_empty() {
        return Err(SyntaxDiagnostic::new(
            DiagnosticKind::Syntax,
            span,
            "expression conversion left unused operands",
        ));
    }
    Ok(result)
}

fn schedule_expression(
    node: SyntaxNode,
    work: &mut Vec<ExpressionFrame>,
    results: &mut Vec<Expression>,
) -> Result<(), SyntaxDiagnostic> {
    if node.kind == SyntaxKind::Unary
        || node.kind == SyntaxKind::Binary
        || node.kind == SyntaxKind::Ternary
        || node.kind == SyntaxKind::Parallel
        || node.kind == SyntaxKind::Group
    {
        schedule_operator(node, work)
    } else {
        schedule_primary(node, work, results)
    }
}

fn schedule_operator(
    node: SyntaxNode,
    work: &mut Vec<ExpressionFrame>,
) -> Result<(), SyntaxDiagnostic> {
    let span = node.span;
    if node.kind == SyntaxKind::Unary {
        let operator = unary_operator(&node)?;
        work.push(ExpressionFrame::Operator(OperatorFrame::Unary(operator, span)));
        work.push(ExpressionFrame::Visit(one_child(node)?));
        return Ok(());
    }
    if node.kind == SyntaxKind::Binary {
        let operator = binary_operator(&node)?;
        let (left, right) = two_children(node)?;
        work.push(ExpressionFrame::Operator(OperatorFrame::Binary(operator, span)));
        work.push(ExpressionFrame::Visit(right));
        work.push(ExpressionFrame::Visit(left));
        return Ok(());
    }
    if node.kind == SyntaxKind::Ternary {
        if node.children.len() != 3 {
            return Err(malformed(&node, "ternary expression needs three operands"));
        }
        work.push(ExpressionFrame::Operator(OperatorFrame::Ternary(span)));
        push_children(node.children, work);
        return Ok(());
    }
    let operator = if node.kind == SyntaxKind::Parallel {
        OperatorFrame::Parallel(span)
    } else if node.kind == SyntaxKind::Group {
        OperatorFrame::Group(span)
    } else {
        return Err(malformed(&node, "expected expression operator"));
    };
    work.push(ExpressionFrame::Operator(operator));
    work.push(ExpressionFrame::Visit(one_child(node)?));
    Ok(())
}

fn schedule_primary(
    mut node: SyntaxNode,
    work: &mut Vec<ExpressionFrame>,
    results: &mut Vec<Expression>,
) -> Result<(), SyntaxDiagnostic> {
    let span = node.span;
    if node.kind == SyntaxKind::Name {
        let identifier = leading_identifier(&mut node)?;
        let access = node.children.into_iter().map(access).collect::<Result<_, _>>()?;
        results.push(Expression::Name { identifier, access, span });
        return Ok(());
    }
    if node.kind == SyntaxKind::Identifier {
        results.push(Expression::Name { identifier: identifier(node)?, access: Vec::new(), span });
        return Ok(());
    }
    if node.kind == SyntaxKind::Number {
        results.push(Expression::Number { text: required_text(&node)?, span });
        return Ok(());
    }
    if node.kind == SyntaxKind::AnonymousCall {
        results.push(Expression::AnonymousCall(anonymous_call(node)?));
        return Ok(());
    }
    if node.kind == SyntaxKind::Error {
        results.push(Expression::Error { span });
        return Ok(());
    }
    schedule_collection(node, work)
}

fn schedule_collection(
    mut node: SyntaxNode,
    work: &mut Vec<ExpressionFrame>,
) -> Result<(), SyntaxDiagnostic> {
    let span = node.span;
    if node.kind == SyntaxKind::Call {
        let name = leading_identifier(&mut node)?;
        work.push(ExpressionFrame::Collection(CollectionFrame::Call(
            name,
            span,
            node.children.len(),
        )));
    } else if node.kind == SyntaxKind::Array {
        work.push(ExpressionFrame::Collection(CollectionFrame::Array(span, node.children.len())));
    } else if node.kind == SyntaxKind::Tuple {
        work.push(ExpressionFrame::Collection(CollectionFrame::Tuple(span, node.children.len())));
    } else {
        return Err(malformed(&node, "expected expression"));
    }
    push_children(node.children, work);
    Ok(())
}

fn push_children(children: Vec<SyntaxNode>, work: &mut Vec<ExpressionFrame>) {
    for child in children.into_iter().rev() {
        work.push(ExpressionFrame::Visit(child));
    }
}

fn take_expression(
    results: &mut Vec<Expression>,
    span: Span,
) -> Result<Expression, SyntaxDiagnostic> {
    results.pop().ok_or_else(|| {
        SyntaxDiagnostic::new(DiagnosticKind::Syntax, span, "missing expression operand")
    })
}

fn take_expressions(
    results: &mut Vec<Expression>,
    span: Span,
    count: usize,
) -> Result<Vec<Expression>, SyntaxDiagnostic> {
    let mut values = Vec::with_capacity(count);
    for _ in 0..count {
        values.push(take_expression(results, span)?);
    }
    values.reverse();
    Ok(values)
}

fn assemble_operator(
    frame: OperatorFrame,
    results: &mut Vec<Expression>,
) -> Result<Expression, SyntaxDiagnostic> {
    match frame {
        OperatorFrame::Unary(operator, span) => Ok(Expression::Unary {
            operator,
            operand: Box::new(take_expression(results, span)?),
            span,
        }),
        OperatorFrame::Binary(operator, span) => {
            let right = take_expression(results, span)?;
            let left = take_expression(results, span)?;
            Ok(Expression::Binary { operator, left: Box::new(left), right: Box::new(right), span })
        }
        OperatorFrame::Ternary(span) => {
            let no = take_expression(results, span)?;
            let yes = take_expression(results, span)?;
            let condition = take_expression(results, span)?;
            Ok(Expression::Ternary {
                condition: Box::new(condition),
                yes: Box::new(yes),
                no: Box::new(no),
                span,
            })
        }
        OperatorFrame::Parallel(span) => {
            Ok(Expression::Parallel { operand: Box::new(take_expression(results, span)?), span })
        }
        OperatorFrame::Group(span) => {
            Ok(Expression::Group { expression: Box::new(take_expression(results, span)?), span })
        }
    }
}

fn assemble_collection(
    frame: CollectionFrame,
    results: &mut Vec<Expression>,
) -> Result<Expression, SyntaxDiagnostic> {
    match frame {
        CollectionFrame::Call(name, span, count) => {
            Ok(Expression::Call { name, arguments: take_expressions(results, span, count)?, span })
        }
        CollectionFrame::Array(span, count) => {
            Ok(Expression::Array { elements: take_expressions(results, span, count)?, span })
        }
        CollectionFrame::Tuple(span, count) => {
            Ok(Expression::Tuple { elements: take_expressions(results, span, count)?, span })
        }
    }
}

fn symbol(node: SyntaxNode) -> Result<DeclaredSymbol, SyntaxDiagnostic> {
    let span = node.span;
    let (name_node, initialization) = if node.kind == SyntaxKind::Assignment {
        let operator = operator(&node)?;
        let (name, value) = two_children(node)?;
        (name, Some((operator, expression(value)?)))
    } else {
        (node, None)
    };
    if name_node.kind != SyntaxKind::Name {
        return Err(malformed(&name_node, "expected declared symbol"));
    }
    let mut name_node = name_node;
    let name = leading_identifier(&mut name_node)?;
    let mut dimensions = Vec::new();
    for index in name_node.children {
        if index.kind != SyntaxKind::Access || index.text.is_some() {
            return Err(malformed(&index, "expected array dimension"));
        }
        dimensions.push(expression(one_child(index)?)?);
    }
    Ok(DeclaredSymbol { name, dimensions, initialization, span })
}

fn tags(node: SyntaxNode) -> Result<Vec<Identifier>, SyntaxDiagnostic> {
    if node.kind != SyntaxKind::Tags {
        return Err(malformed(&node, "expected tags"));
    }
    identifiers(node.children)
}

fn declaration_header(mut node: SyntaxNode) -> Result<DeclarationKind, SyntaxDiagnostic> {
    let direction_first = node.kind == SyntaxKind::DirectionFirstSignalHeader
        || node.kind == SyntaxKind::DirectionFirstBusHeader;
    let is_signal = node.kind == SyntaxKind::SignalHeader
        || node.kind == SyntaxKind::DirectionFirstSignalHeader;
    let is_bus =
        node.kind == SyntaxKind::BusHeader || node.kind == SyntaxKind::DirectionFirstBusHeader;
    if !is_signal && !is_bus {
        return Err(malformed(&node, "expected declaration header"));
    }
    let type_name = if is_bus {
        if direction_first {
            if node.children.len() < 2 {
                return Err(malformed(&node, "bus declaration needs a type name"));
            }
            Some(identifier(node.children.remove(1))?)
        } else {
            Some(leading_identifier(&mut node)?)
        }
    } else {
        None
    };
    let mut direction_value = None;
    let mut tag_values = Vec::new();
    let mut arguments = ArgumentList::Omitted;
    for child in node.children {
        match child.kind {
            SyntaxKind::Direction => direction_value = Some(direction(&child)?),
            SyntaxKind::Tags => tag_values = tags(child)?,
            SyntaxKind::Arguments if is_bus => {
                arguments = ArgumentList::Parenthesized(
                    child.children.into_iter().map(expression).collect::<Result<_, _>>()?,
                );
            }
            _ => return Err(malformed(&child, "unexpected signal header child")),
        }
    }
    let direction = match (direction_first, direction_value) {
        (true, Some(direction)) => DirectionSyntax::Before(direction),
        (false, Some(direction)) => DirectionSyntax::After(direction),
        (false, None) => DirectionSyntax::Unspecified,
        (true, None) => {
            return Err(SyntaxDiagnostic::new(
                DiagnosticKind::Syntax,
                node.span,
                "direction-first declaration has no direction",
            ))
        }
    };
    if let Some(type_name) = type_name {
        Ok(DeclarationKind::Bus { type_name, arguments, direction, tags: tag_values })
    } else {
        Ok(DeclarationKind::Signal { direction, tags: tag_values })
    }
}

fn declaration(node: SyntaxNode) -> Result<Declaration, SyntaxDiagnostic> {
    let span = node.span;
    let symbol_syntax = if node.kind == SyntaxKind::TupleDeclaration {
        SymbolSyntax::Tuple
    } else {
        SymbolSyntax::List
    };
    let mut children = node.children.into_iter();
    let kind = match node.text.as_deref() {
        Some("var") => DeclarationKind::Variable,
        Some("component") => DeclarationKind::Component,
        _ => {
            let header = children.next().ok_or_else(|| {
                SyntaxDiagnostic::new(DiagnosticKind::Syntax, span, "missing declaration header")
            })?;
            declaration_header(header)?
        }
    };
    let mut symbols = Vec::new();
    let mut tuple_initialization = None;
    for child in children {
        if child.kind == SyntaxKind::Assignment && child.children.len() == 1 {
            let assignment = operator(&child)?;
            let expression_node = one_child(child)?;
            tuple_initialization = Some((assignment, expression(expression_node)?));
        } else {
            symbols.push(symbol(child)?);
        }
    }
    if symbols.is_empty() {
        return Err(SyntaxDiagnostic::new(
            DiagnosticKind::Syntax,
            span,
            "declaration requires at least one symbol",
        ));
    }
    Ok(Declaration { kind, symbol_syntax, symbols, tuple_initialization, span })
}

fn assignment(node: SyntaxNode) -> Result<Statement, SyntaxDiagnostic> {
    let span = node.span;
    if node.text.as_deref() == Some("++") || node.text.as_deref() == Some("--") {
        let operator = postfix_operator(&node)?;
        let target = expression(one_child(node)?)?;
        return Ok(Statement::PostfixUpdate { target, operator, span });
    }
    let operator = operator(&node)?;
    let (left, right) = two_children(node)?;
    let (target, value) = if operator == AssignmentOperator::ReverseWitness
        || operator == AssignmentOperator::ReverseConstraint
    {
        (right, left)
    } else {
        (left, right)
    };
    Ok(Statement::Assignment {
        target: expression(target)?,
        operator,
        value: expression(value)?,
        span,
    })
}

fn conditional(node: SyntaxNode) -> Result<Statement, SyntaxDiagnostic> {
    let span = node.span;
    if node.children.len() < 2 || node.children.len() > 3 {
        return Err(malformed(&node, "invalid conditional branches"));
    }
    let mut children = node.children.into_iter();
    let condition = children
        .next()
        .ok_or_else(|| SyntaxDiagnostic::new(DiagnosticKind::Syntax, span, "missing condition"))?;
    let then_branch = children.next().ok_or_else(|| {
        SyntaxDiagnostic::new(DiagnosticKind::Syntax, span, "missing then branch")
    })?;
    let else_branch = children.next().map(statement).transpose()?.map(Box::new);
    Ok(Statement::If {
        condition: expression(condition)?,
        then_branch: Box::new(statement(then_branch)?),
        else_branch,
        span,
    })
}

fn loop_statement(node: SyntaxNode) -> Result<Statement, SyntaxDiagnostic> {
    let span = node.span;
    match node.children.len() {
        2 => {
            let (condition, body) = two_children(node)?;
            Ok(Statement::While {
                condition: expression(condition)?,
                body: Box::new(statement(body)?),
                span,
            })
        }
        4 => {
            let mut children = node.children.into_iter();
            let initializer = children.next().ok_or_else(|| {
                SyntaxDiagnostic::new(DiagnosticKind::Syntax, span, "missing for initializer")
            })?;
            let condition = children.next().ok_or_else(|| {
                SyntaxDiagnostic::new(DiagnosticKind::Syntax, span, "missing for condition")
            })?;
            let step = children.next().ok_or_else(|| {
                SyntaxDiagnostic::new(DiagnosticKind::Syntax, span, "missing for step")
            })?;
            let body = children.next().ok_or_else(|| {
                SyntaxDiagnostic::new(DiagnosticKind::Syntax, span, "missing for body")
            })?;
            Ok(Statement::For {
                initializer: Box::new(statement(initializer)?),
                condition: expression(condition)?,
                step: Box::new(statement(step)?),
                body: Box::new(statement(body)?),
                span,
            })
        }
        _ => Err(malformed(&node, "invalid loop operands")),
    }
}

fn block(node: SyntaxNode) -> Result<Block, SyntaxDiagnostic> {
    if node.kind != SyntaxKind::Block {
        return Err(malformed(&node, "expected block"));
    }
    Ok(Block {
        span: node.span,
        statements: node.children.into_iter().map(statement).collect::<Result<_, _>>()?,
    })
}

fn statement(node: SyntaxNode) -> Result<Statement, SyntaxDiagnostic> {
    let span = node.span;
    match node.kind {
        SyntaxKind::Block => Ok(Statement::Block(block(node)?)),
        SyntaxKind::Declaration | SyntaxKind::TupleDeclaration => {
            Ok(Statement::Declaration(declaration(node)?))
        }
        SyntaxKind::Assignment => assignment(node),
        SyntaxKind::Constraint => {
            let (left, right) = two_children(node)?;
            Ok(Statement::Constraint { left: expression(left)?, right: expression(right)?, span })
        }
        SyntaxKind::Conditional => conditional(node),
        SyntaxKind::Loop => loop_statement(node),
        SyntaxKind::Return => Ok(Statement::Return { value: expression(one_child(node)?)?, span }),
        SyntaxKind::Assert => {
            Ok(Statement::Assert { condition: expression(one_child(node)?)?, span })
        }
        SyntaxKind::Log => {
            let arguments = node
                .children
                .into_iter()
                .map(|child| {
                    if child.kind == SyntaxKind::String {
                        Ok(LogArgument::String { value: required_text(&child)?, span: child.span })
                    } else {
                        expression(child).map(LogArgument::Expression)
                    }
                })
                .collect::<Result<_, SyntaxDiagnostic>>()?;
            Ok(Statement::Log { arguments, span })
        }
        SyntaxKind::ExpressionStatement => {
            let call = one_child(node)?;
            if call.kind != SyntaxKind::AnonymousCall {
                return Err(malformed(
                    &call,
                    "only anonymous calls are valid expression statements",
                ));
            }
            Ok(Statement::AnonymousCall { call: anonymous_call(call)?, span })
        }
        SyntaxKind::Error | SyntaxKind::RecoveredStatement => Ok(Statement::Error { span }),
        _ => Err(malformed(&node, "expected statement")),
    }
}

fn version(text: &str, span: Span) -> Result<Version, SyntaxDiagnostic> {
    let mut parts = text.split('.');
    let parse_part = |part: Option<&str>| {
        part.and_then(|part| part.parse::<u32>().ok()).ok_or_else(|| {
            SyntaxDiagnostic::new(
                DiagnosticKind::InvalidNumber,
                span,
                "Circom version contains an out-of-range component",
            )
        })
    };
    let major = parse_part(parts.next())?;
    let minor = parse_part(parts.next())?;
    let patch = parse_part(parts.next())?;
    if parts.next().is_some() {
        return Err(SyntaxDiagnostic::new(
            DiagnosticKind::InvalidNumber,
            span,
            "Circom version has too many components",
        ));
    }
    Ok(Version::new(major, minor, patch))
}

fn definition(node: SyntaxNode) -> Result<Definition, SyntaxDiagnostic> {
    let span = node.span;
    let mut name = None;
    let mut parameters = ArgumentList::Omitted;
    let mut body = None;
    let mut custom = false;
    let mut external = false;
    let mut parallel = false;
    for child in node.children {
        match child.kind {
            SyntaxKind::Identifier => name = Some(identifier(child)?),
            SyntaxKind::Parameters => {
                parameters = ArgumentList::Parenthesized(identifiers(child.children)?);
            }
            SyntaxKind::Modifier => match child.text.as_deref() {
                Some("custom") => custom = true,
                Some("extern_c") => external = true,
                Some("parallel") => parallel = true,
                _ => return Err(malformed(&child, "invalid template modifier")),
            },
            SyntaxKind::Block => body = Some(block(child)?),
            _ => return Err(malformed(&child, "invalid definition child")),
        }
    }
    let body = body.ok_or_else(|| {
        SyntaxDiagnostic::new(DiagnosticKind::Syntax, span, "definition has no body")
    })?;
    let name = name.ok_or_else(|| {
        SyntaxDiagnostic::new(DiagnosticKind::Syntax, span, "definition has no name")
    })?;
    let kind = match node.kind {
        SyntaxKind::Function => DefinitionKind::Function,
        SyntaxKind::Template => DefinitionKind::Template { custom, external, parallel },
        SyntaxKind::Bus => DefinitionKind::Bus,
        _ => {
            return Err(SyntaxDiagnostic::new(DiagnosticKind::Syntax, span, "expected definition"))
        }
    };
    Ok(Definition { kind, name, parameters, body, span })
}

fn main_item(node: SyntaxNode) -> Result<Item, SyntaxDiagnostic> {
    let span = node.span;
    let mut public = Vec::new();
    let mut instance = None;
    for child in node.children {
        if child.kind == SyntaxKind::PublicList {
            public = identifiers(child.children)?;
        } else {
            if instance.is_some() {
                return Err(malformed(&child, "multiple main expressions"));
            }
            instance = Some(expression(child)?);
        }
    }
    let instance = instance.ok_or_else(|| {
        SyntaxDiagnostic::new(DiagnosticKind::Syntax, span, "missing main expression")
    })?;
    Ok(Item::Main { public, instance, span })
}

pub(crate) fn item(node: SyntaxNode) -> Result<Item, SyntaxDiagnostic> {
    let span = node.span;
    match node.kind {
        SyntaxKind::Pragma => {
            let text = node.text.as_deref();
            Ok(Item::Pragma {
                pragma: if let Some(text) = text {
                    Pragma::Version(version(text, span)?)
                } else {
                    Pragma::CustomTemplates
                },
                span,
            })
        }
        SyntaxKind::Include => Ok(Item::Include { path: required_text(&node)?, span }),
        SyntaxKind::Function | SyntaxKind::Template | SyntaxKind::Bus => {
            Ok(Item::Definition(definition(node)?))
        }
        SyntaxKind::Main => main_item(node),
        SyntaxKind::Error => Ok(Item::Error { span }),
        _ => Err(malformed(&node, "expected top-level item")),
    }
}
