use crate::frontend::source::{DiagnosticKind, Span, SyntaxDiagnostic, Version};
use crate::frontend::parsed::{
    unpack, AnnotationId, ParseContext, Parsed, ParsedItem, Recovery, SourceForm,
};
use crate::frontend::ast::{
    ArgumentList, AssignmentOperator, Block, Declaration, DeclarationKind, DeclaredSymbol,
    Definition, DefinitionKind, Expression, Identifier, Item, Pragma, Statement, SymbolSyntax,
};

pub(crate) enum TemplateModifier {
    Custom,
    External,
    Parallel,
}

pub(crate) struct DefinitionParts {
    pub name: Parsed<Identifier>,
    pub parameters: Option<Parsed<Vec<Identifier>>>,
    pub body: Parsed<Block>,
}

pub(crate) struct ForParts {
    pub initializer: Parsed<Statement>,
    pub condition: Parsed<Expression>,
    pub step: Parsed<Statement>,
    pub body: Parsed<Statement>,
}

pub(crate) struct DeclarationParts {
    pub header: Parsed<DeclarationKind>,
    pub syntax: SymbolSyntax,
    pub symbols: Vec<Parsed<DeclaredSymbol>>,
    pub initialization: Option<Parsed<(AssignmentOperator, Expression)>>,
}

pub(super) fn arguments<T>(
    arguments: Option<Parsed<Vec<T>>>,
    children: &mut Vec<AnnotationId>,
) -> ArgumentList<T> {
    let Some(arguments) = arguments else { return ArgumentList::Omitted };
    children.push(arguments.annotation);
    ArgumentList::Parenthesized(arguments.value)
}

impl ParseContext {
    pub fn version_item(&mut self, span: Span, parts: [String; 3]) -> ParsedItem {
        let [major, minor, patch] = parts;
        let Ok(major) = major.parse() else { return self.invalid_version(span) };
        let Ok(minor) = minor.parse() else { return self.invalid_version(span) };
        let Ok(patch) = patch.parse() else { return self.invalid_version(span) };
        let pragma = Pragma::Version(Version::new(major, minor, patch));
        ParsedItem::Ready(self.plain(Item::Pragma { pragma, span }, span, Vec::new()))
    }

    fn invalid_version(&mut self, span: Span) -> ParsedItem {
        let diagnostic = SyntaxDiagnostic::new(
            DiagnosticKind::InvalidNumber,
            span,
            "Circom version contains an out-of-range component",
        );
        let annotation = self.plain((), span, Vec::new()).annotation;
        ParsedItem::InvalidVersion { annotation, diagnostic }
    }

    pub fn definition(
        &mut self,
        kind: DefinitionKind,
        span: Span,
        parts: DefinitionParts,
        mut children: Vec<AnnotationId>,
    ) -> ParsedItem {
        children.push(parts.name.annotation);
        let parameters = arguments(parts.parameters, &mut children);
        children.push(parts.body.annotation);
        let form = match kind {
            DefinitionKind::Bus => SourceForm::Feature(Version::new(2, 2, 0)),
            DefinitionKind::Function | DefinitionKind::Template { .. } => SourceForm::Plain,
        };
        let definition =
            Definition { kind, name: parts.name.value, parameters, body: parts.body.value, span };
        ParsedItem::Ready(self.annotate(Item::Definition(definition), span, children, form))
    }

    pub fn template(
        &mut self,
        span: Span,
        modifiers: Vec<Parsed<TemplateModifier>>,
        parts: DefinitionParts,
    ) -> ParsedItem {
        let mut custom = false;
        let mut external = false;
        let mut parallel = false;
        let mut children = Vec::with_capacity(modifiers.len() + 3);
        for modifier in modifiers {
            children.push(modifier.annotation);
            match modifier.value {
                TemplateModifier::Custom => custom = true,
                TemplateModifier::External => external = true,
                TemplateModifier::Parallel => parallel = true,
            }
        }
        self.definition(
            DefinitionKind::Template { custom, external, parallel },
            span,
            parts,
            children,
        )
    }

    pub fn main_item(
        &mut self,
        span: Span,
        public: Option<Parsed<Vec<Identifier>>>,
        instance: Parsed<Expression>,
    ) -> ParsedItem {
        let mut children = Vec::new();
        let public = if let Some(public) = public {
            children.push(public.annotation);
            public.value
        } else {
            Vec::new()
        };
        children.push(instance.annotation);
        ParsedItem::Ready(self.plain(
            Item::Main { public, instance: instance.value, span },
            span,
            children,
        ))
    }

    pub fn symbol(
        &mut self,
        span: Span,
        name: Parsed<Identifier>,
        dimensions: Vec<Parsed<Expression>>,
    ) -> Parsed<DeclaredSymbol> {
        let (dimensions, dimension_children) = unpack(dimensions);
        let mut children = vec![name.annotation];
        children.extend(dimension_children);
        let symbol = DeclaredSymbol { name: name.value, dimensions, initialization: None, span };
        self.annotate(symbol, span, children, SourceForm::PotentialBus)
    }

    pub fn initialized_symbol(
        &mut self,
        span: Span,
        symbol: Parsed<DeclaredSymbol>,
        operator: AssignmentOperator,
        value: Parsed<Expression>,
    ) -> Parsed<DeclaredSymbol> {
        let children = vec![symbol.annotation, value.annotation];
        let symbol =
            DeclaredSymbol { initialization: Some((operator, value.value)), span, ..symbol.value };
        self.plain(symbol, span, children)
    }

    pub fn declaration(&mut self, span: Span, parts: DeclarationParts) -> Parsed<Declaration> {
        let (symbols, symbol_children) = unpack(parts.symbols);
        let mut children = vec![parts.header.annotation];
        children.extend(symbol_children);
        let tuple_initialization = parts.initialization.map(|initialization| {
            children.push(initialization.annotation);
            initialization.value
        });
        let form = match parts.syntax {
            SymbolSyntax::List => SourceForm::Plain,
            SymbolSyntax::Tuple => SourceForm::Feature(Version::new(2, 1, 0)),
        };
        let declaration = Declaration {
            kind: parts.header.value,
            symbol_syntax: parts.syntax,
            symbols,
            tuple_initialization,
            span,
        };
        self.annotate(declaration, span, children, form)
    }

    pub fn assignment(
        &mut self,
        span: Span,
        left: Parsed<Expression>,
        operator: AssignmentOperator,
        right: Parsed<Expression>,
    ) -> Parsed<Statement> {
        let children = vec![left.annotation, right.annotation];
        let (target, value) = if operator == AssignmentOperator::ReverseWitness
            || operator == AssignmentOperator::ReverseConstraint
        {
            (right.value, left.value)
        } else {
            (left.value, right.value)
        };
        self.plain(Statement::Assignment { target, operator, value, span }, span, children)
    }

    pub fn conditional(
        &mut self,
        span: Span,
        condition: Parsed<Expression>,
        then_branch: Parsed<Statement>,
        else_branch: Option<Parsed<Statement>>,
    ) -> Parsed<Statement> {
        let mut children = vec![condition.annotation, then_branch.annotation];
        let else_branch = else_branch.map(|branch| {
            children.push(branch.annotation);
            Box::new(branch.value)
        });
        let statement = Statement::If {
            condition: condition.value,
            then_branch: Box::new(then_branch.value),
            else_branch,
            span,
        };
        self.plain(statement, span, children)
    }

    pub fn for_statement(&mut self, span: Span, parts: ForParts) -> Parsed<Statement> {
        let children = vec![
            parts.initializer.annotation,
            parts.condition.annotation,
            parts.step.annotation,
            parts.body.annotation,
        ];
        let statement = Statement::For {
            initializer: Box::new(parts.initializer.value),
            condition: parts.condition.value,
            step: Box::new(parts.step.value),
            body: Box::new(parts.body.value),
            span,
        };
        self.plain(statement, span, children)
    }

    pub fn expression_statement(
        &mut self,
        span: Span,
        expression: Parsed<Expression>,
    ) -> Parsed<Statement> {
        let children = vec![expression.annotation];
        let Expression::AnonymousCall(call) = expression.value else {
            return self.annotate(
                Statement::Error { span },
                span,
                children,
                SourceForm::Recovery(Recovery::ExpressionStatement),
            );
        };
        self.plain(Statement::AnonymousCall { call, span }, span, children)
    }
}
