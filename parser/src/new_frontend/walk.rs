use super::ast::Span;
use super::typed::{
    Access, AnonymousCallExpr, AnonymousInput, Block, Declaration, DeclarationKind, DeclaredSymbol,
    Definition, DirectionSyntax, Expression, Identifier, Item, LogArgument, SourceAst, Statement,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SyntaxCategory {
    Trivia,
    Item,
    Definition,
    Block,
    Statement,
    Declaration,
    Symbol,
    Expression,
    Identifier,
    Access,
    Direction,
    Tag,
}

pub trait WalkSyntax {
    /// Visits this node and descendants with the containing node's span.
    fn walk_syntax(
        &self,
        parent: Option<Span>,
        visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
    );
}

fn emit(
    category: SyntaxCategory,
    span: Span,
    parent: Option<Span>,
    visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
) {
    visitor(category, span, parent);
}

impl WalkSyntax for SourceAst {
    fn walk_syntax(
        &self,
        _parent: Option<Span>,
        visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
    ) {
        for trivia in &self.trivia {
            emit(SyntaxCategory::Trivia, trivia.span, None, visitor);
        }
        for item in &self.items {
            item.walk_syntax(None, visitor);
        }
    }
}

impl WalkSyntax for Item {
    fn walk_syntax(
        &self,
        parent: Option<Span>,
        visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
    ) {
        let span = self.span();
        emit(SyntaxCategory::Item, span, parent, visitor);
        match self {
            Self::Definition(definition) => definition.walk_syntax(Some(span), visitor),
            Self::Main { public, instance, .. } => {
                for name in public {
                    name.walk_syntax(Some(span), visitor);
                }
                instance.walk_syntax(Some(span), visitor);
            }
            Self::Pragma { .. } | Self::Include { .. } | Self::Error { .. } => {}
        }
    }
}

impl WalkSyntax for Identifier {
    fn walk_syntax(
        &self,
        parent: Option<Span>,
        visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
    ) {
        emit(SyntaxCategory::Identifier, self.span, parent, visitor);
    }
}

impl WalkSyntax for Definition {
    fn walk_syntax(
        &self,
        parent: Option<Span>,
        visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
    ) {
        emit(SyntaxCategory::Definition, self.span, parent, visitor);
        self.name.walk_syntax(Some(self.span), visitor);
        for parameter in self.parameters.values() {
            parameter.walk_syntax(Some(self.span), visitor);
        }
        self.body.walk_syntax(Some(self.span), visitor);
    }
}

impl WalkSyntax for Block {
    fn walk_syntax(
        &self,
        parent: Option<Span>,
        visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
    ) {
        emit(SyntaxCategory::Block, self.span, parent, visitor);
        for statement in &self.statements {
            statement.walk_syntax(Some(self.span), visitor);
        }
    }
}

impl WalkSyntax for Statement {
    fn walk_syntax(
        &self,
        parent: Option<Span>,
        visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
    ) {
        let span = self.span();
        emit(SyntaxCategory::Statement, span, parent, visitor);
        match self {
            Self::Block(block) => block.walk_syntax(Some(span), visitor),
            Self::Declaration(declaration) => declaration.walk_syntax(Some(span), visitor),
            Self::Assignment { target, value, .. } => {
                target.walk_syntax(Some(span), visitor);
                value.walk_syntax(Some(span), visitor);
            }
            Self::PostfixUpdate { target, .. } => target.walk_syntax(Some(span), visitor),
            Self::Constraint { left, right, .. } => {
                left.walk_syntax(Some(span), visitor);
                right.walk_syntax(Some(span), visitor);
            }
            Self::If { condition, then_branch, else_branch, .. } => {
                condition.walk_syntax(Some(span), visitor);
                then_branch.walk_syntax(Some(span), visitor);
                if let Some(else_branch) = else_branch {
                    else_branch.walk_syntax(Some(span), visitor);
                }
            }
            Self::For { initializer, condition, step, body, .. } => {
                initializer.walk_syntax(Some(span), visitor);
                condition.walk_syntax(Some(span), visitor);
                step.walk_syntax(Some(span), visitor);
                body.walk_syntax(Some(span), visitor);
            }
            Self::While { condition, body, .. } => {
                condition.walk_syntax(Some(span), visitor);
                body.walk_syntax(Some(span), visitor);
            }
            Self::Return { value, .. } => value.walk_syntax(Some(span), visitor),
            Self::Assert { condition, .. } => condition.walk_syntax(Some(span), visitor),
            Self::Log { arguments, .. } => {
                for argument in arguments {
                    argument.walk_syntax(Some(span), visitor);
                }
            }
            Self::AnonymousCall { call, .. } => call.walk_syntax(Some(span), visitor),
            Self::Error { .. } => {}
        }
    }
}

impl WalkSyntax for LogArgument {
    fn walk_syntax(
        &self,
        parent: Option<Span>,
        visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
    ) {
        match self {
            Self::String { span, .. } => emit(SyntaxCategory::Expression, *span, parent, visitor),
            Self::Expression(expression) => expression.walk_syntax(parent, visitor),
        }
    }
}

impl WalkSyntax for Declaration {
    fn walk_syntax(
        &self,
        parent: Option<Span>,
        visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
    ) {
        emit(SyntaxCategory::Declaration, self.span, parent, visitor);
        match &self.kind {
            DeclarationKind::Signal { direction, tags } => {
                walk_direction(direction, self.span, visitor);
                for tag in tags {
                    tag.walk_syntax(Some(self.span), visitor);
                }
            }
            DeclarationKind::Bus { type_name, arguments, direction, tags } => {
                type_name.walk_syntax(Some(self.span), visitor);
                for argument in arguments.values() {
                    argument.walk_syntax(Some(self.span), visitor);
                }
                walk_direction(direction, self.span, visitor);
                for tag in tags {
                    tag.walk_syntax(Some(self.span), visitor);
                }
            }
            DeclarationKind::Variable | DeclarationKind::Component => {}
        }
        for symbol in &self.symbols {
            symbol.walk_syntax(Some(self.span), visitor);
        }
        if let Some((_, expression)) = &self.tuple_initialization {
            expression.walk_syntax(Some(self.span), visitor);
        }
    }
}

fn walk_direction(
    direction: &DirectionSyntax,
    parent: Span,
    visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
) {
    match direction {
        DirectionSyntax::Before(value) | DirectionSyntax::After(value) => {
            emit(SyntaxCategory::Direction, value.span, Some(parent), visitor);
        }
        DirectionSyntax::Unspecified => {}
    }
}

impl WalkSyntax for DeclaredSymbol {
    fn walk_syntax(
        &self,
        parent: Option<Span>,
        visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
    ) {
        emit(SyntaxCategory::Symbol, self.span, parent, visitor);
        self.name.walk_syntax(Some(self.span), visitor);
        for dimension in &self.dimensions {
            dimension.walk_syntax(Some(self.span), visitor);
        }
        if let Some((_, expression)) = &self.initialization {
            expression.walk_syntax(Some(self.span), visitor);
        }
    }
}

impl WalkSyntax for Access {
    fn walk_syntax(
        &self,
        parent: Option<Span>,
        visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
    ) {
        match self {
            Self::Field { field, span } => {
                emit(SyntaxCategory::Access, *span, parent, visitor);
                field.walk_syntax(Some(*span), visitor);
            }
            Self::Index { expression, span } => {
                emit(SyntaxCategory::Access, *span, parent, visitor);
                expression.walk_syntax(Some(*span), visitor);
            }
        }
    }
}

impl WalkSyntax for AnonymousInput {
    fn walk_syntax(
        &self,
        parent: Option<Span>,
        visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
    ) {
        match self {
            Self::Positional(expression) => expression.walk_syntax(parent, visitor),
            Self::Named { name, value, span, .. } => {
                emit(SyntaxCategory::Expression, *span, parent, visitor);
                name.walk_syntax(Some(*span), visitor);
                value.walk_syntax(Some(*span), visitor);
            }
        }
    }
}

impl WalkSyntax for AnonymousCallExpr {
    fn walk_syntax(
        &self,
        parent: Option<Span>,
        visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
    ) {
        emit(SyntaxCategory::Expression, self.span, parent, visitor);
        walk_anonymous_children(self, visitor);
    }
}

fn walk_anonymous_children(
    call: &AnonymousCallExpr,
    visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
) {
    call.name.walk_syntax(Some(call.span), visitor);
    for parameter in &call.parameters {
        parameter.walk_syntax(Some(call.span), visitor);
    }
    for input in &call.inputs {
        input.walk_syntax(Some(call.span), visitor);
    }
}

impl WalkSyntax for Expression {
    fn walk_syntax(
        &self,
        parent: Option<Span>,
        visitor: &mut dyn FnMut(SyntaxCategory, Span, Option<Span>),
    ) {
        let span = self.span();
        emit(SyntaxCategory::Expression, span, parent, visitor);
        match self {
            Self::Name { identifier, access, .. } => {
                identifier.walk_syntax(Some(span), visitor);
                for access in access {
                    access.walk_syntax(Some(span), visitor);
                }
            }
            Self::Call { name, arguments, .. } => {
                name.walk_syntax(Some(span), visitor);
                for argument in arguments {
                    argument.walk_syntax(Some(span), visitor);
                }
            }
            Self::AnonymousCall(call) => walk_anonymous_children(call, visitor),
            Self::Array { elements, .. } | Self::Tuple { elements, .. } => {
                for element in elements {
                    element.walk_syntax(Some(span), visitor);
                }
            }
            Self::Unary { operand, .. } | Self::Parallel { operand, .. } => {
                operand.walk_syntax(Some(span), visitor);
            }
            Self::Binary { left, right, .. } => {
                left.walk_syntax(Some(span), visitor);
                right.walk_syntax(Some(span), visitor);
            }
            Self::Ternary { condition, yes, no, .. } => {
                condition.walk_syntax(Some(span), visitor);
                yes.walk_syntax(Some(span), visitor);
                no.walk_syntax(Some(span), visitor);
            }
            Self::Group { expression, .. } => expression.walk_syntax(Some(span), visitor),
            Self::Number { .. } | Self::Error { .. } => {}
        }
    }
}
