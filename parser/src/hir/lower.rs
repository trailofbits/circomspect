use std::collections::BTreeMap;

use super::{
    AccessPath, AccessStep, AnonymousInputEffect, AnonymousInputTarget, ArrayIndex, BlockId, Bus,
    BusId, BusTarget, CallTarget, ComponentId, DefinitionKind, DefinitionRef, Effect, ExprId,
    ExprKind, HirProject, IncompleteReason, IncompleteRegion, Knownness, LoweredProject, Main,
    SemanticCode, SemanticDiagnostic, Severity, SymbolId, SymbolKind, Template, TemplateId,
    Function, FunctionId,
};
use crate::new_frontend::{
    Access, AnonymousCallExpr, AnonymousInput, AssignmentOperator, Declaration, DeclarationKind,
    Definition, DefinitionKind as SourceDefinitionKind, DirectionSyntax, Expression, Identifier,
    Item, LoadedProject, LogArgument, PortDirection, Span, Statement, DiagnosticKind,
    InputAssignmentOperator,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ValueType {
    Plain,
    Bus(BusId),
    Component(TemplateId),
    Unknown,
}

#[derive(Default)]
struct Scopes {
    stack: Vec<BTreeMap<String, SymbolId>>,
}

impl Scopes {
    fn enter(&mut self) {
        self.stack.push(BTreeMap::new());
    }
    fn leave(&mut self) {
        self.stack.pop();
    }
    fn current(&self, name: &str) -> Option<SymbolId> {
        self.stack.last().and_then(|scope| scope.get(name).copied())
    }
    fn resolve(&self, name: &str) -> Option<SymbolId> {
        self.stack.iter().rev().find_map(|scope| scope.get(name).copied())
    }
    fn outer(&self, name: &str) -> Option<SymbolId> {
        self.stack.iter().rev().skip(1).find_map(|scope| scope.get(name).copied())
    }
    fn insert(&mut self, name: String, symbol: SymbolId) {
        if let Some(scope) = self.stack.last_mut() {
            scope.insert(name, symbol);
        }
    }
}

struct Lowerer<'a> {
    source: &'a LoadedProject,
    hir: HirProject,
    diagnostics: Vec<SemanticDiagnostic>,
    incomplete: Vec<IncompleteRegion>,
    expression_types: Vec<ValueType>,
    array_types: BTreeMap<(usize, usize, usize), ValueType>,
    components: BTreeMap<SymbolId, ComponentId>,
    predeclared_ports: BTreeMap<(usize, usize, usize), SymbolId>,
    scopes: Scopes,
    current_definition: Option<DefinitionRef>,
}

impl Lowerer<'_> {
    fn diagnostic(&mut self, code: SemanticCode, severity: Severity, span: Span, message: String) {
        self.diagnostics.push(SemanticDiagnostic {
            code,
            severity,
            span,
            message,
            expected_kind: None,
            actual_kind: None,
        });
    }

    fn incomplete(&mut self, span: Span, reason: IncompleteReason) {
        self.incomplete.push(IncompleteRegion { span, reason });
    }

    fn add_expression(
        &mut self,
        kind: ExprKind,
        knownness: Knownness,
        span: Span,
        ty: ValueType,
    ) -> ExprId {
        let id = self.hir.add_expr(kind, knownness, span);
        self.expression_types.push(ty);
        id
    }

    fn expression_type(&self, id: ExprId) -> ValueType {
        self.expression_types.get(id.index).copied().unwrap_or(ValueType::Unknown)
    }

    fn knownness(&self, id: ExprId) -> Knownness {
        self.hir.expression(id).map_or(Knownness::Opaque, |expr| expr.knownness)
    }

    fn expect_compile_time(&mut self, expression: ExprId, span: Span, dimension: bool) {
        let knownness = self.knownness(expression);
        if knownness == Knownness::WitnessDependent && dimension {
            self.diagnostic(
                SemanticCode::NonConstantArrayLength,
                Severity::Error,
                span,
                "array dimension depends on a witness value".into(),
            );
        }
        if !knownness.is_compile_time() {
            self.incomplete(span, IncompleteReason::NonCompileTime);
        }
    }

    fn index_definitions(&mut self) {
        for file in &self.source.files {
            for item in &file.outcome.ast.items {
                let Item::Definition(definition) = item else { continue };
                let body = self.hir.add_block(definition.body.span);
                let name = definition.name.name.clone();
                let reference = match definition.kind {
                    SourceDefinitionKind::Function => {
                        let id = FunctionId::new(self.hir.functions.len(), self.hir.key);
                        self.hir.functions.push(Function {
                            id,
                            name: name.clone(),
                            parameters: Vec::new(),
                            body,
                            span: definition.span,
                        });
                        DefinitionRef::Function(id)
                    }
                    SourceDefinitionKind::Template { custom, external, .. } => {
                        let id = TemplateId::new(self.hir.templates.len(), self.hir.key);
                        self.hir.templates.push(Template {
                            id,
                            name: name.clone(),
                            parameters: Vec::new(),
                            ports: Vec::new(),
                            body,
                            custom,
                            external,
                            span: definition.span,
                        });
                        DefinitionRef::Template(id)
                    }
                    SourceDefinitionKind::Bus => {
                        let id = BusId::new(self.hir.buses.len(), self.hir.key);
                        self.hir.buses.push(Bus {
                            id,
                            name: name.clone(),
                            parameters: Vec::new(),
                            ports: Vec::new(),
                            body,
                            span: definition.span,
                        });
                        DefinitionRef::Bus(id)
                    }
                };
                self.hir.definitions.entry(name).or_default().push(reference);
            }
        }
        self.report_duplicate_definitions();
    }

    fn report_duplicate_definitions(&mut self) {
        let duplicates: Vec<_> = self
            .hir
            .definitions
            .iter()
            .filter(|(_, definitions)| definitions.len() > 1)
            .map(|(name, definitions)| (name.clone(), definitions.clone()))
            .collect();
        for (name, definitions) in duplicates {
            let same_kind = definitions.iter().all(|reference| {
                Self::definition_kind(*reference) == Self::definition_kind(definitions[0])
            });
            for reference in definitions {
                let code = if same_kind {
                    match reference {
                        DefinitionRef::Function(_) => SemanticCode::DuplicateFunction,
                        DefinitionRef::Template(_) => SemanticCode::DuplicateTemplate,
                        DefinitionRef::Bus(_) => SemanticCode::DuplicateSymbol,
                    }
                } else {
                    SemanticCode::DuplicateSymbol
                };
                let span = self.definition_span(reference);
                self.diagnostic(
                    code,
                    Severity::Error,
                    span,
                    format!("duplicate global name `{name}`"),
                );
                self.incomplete(span, IncompleteReason::AmbiguousReference(name.clone()));
            }
        }
    }

    fn definition_kind(reference: DefinitionRef) -> DefinitionKind {
        match reference {
            DefinitionRef::Function(_) => DefinitionKind::Function,
            DefinitionRef::Template(_) => DefinitionKind::Template,
            DefinitionRef::Bus(_) => DefinitionKind::Bus,
        }
    }

    fn definition_span(&self, reference: DefinitionRef) -> Span {
        match reference {
            DefinitionRef::Function(id) => self.hir.functions[id.index].span,
            DefinitionRef::Template(id) => self.hir.templates[id.index].span,
            DefinitionRef::Bus(id) => self.hir.buses[id.index].span,
        }
    }

    fn parameters(&mut self, definition: &Definition) -> Vec<SymbolId> {
        let mut seen = BTreeMap::new();
        definition
            .parameters
            .values()
            .iter()
            .map(|parameter| {
                if seen.insert(parameter.name.as_str(), parameter.span).is_some() {
                    self.diagnostic(
                        SemanticCode::ParameterCollision,
                        Severity::Warning,
                        parameter.span,
                        format!("duplicate parameter `{}`", parameter.name),
                    );
                    self.incomplete(
                        parameter.span,
                        IncompleteReason::AmbiguousReference(parameter.name.clone()),
                    );
                }
                self.hir.add_symbol(parameter.name.clone(), SymbolKind::Parameter, parameter.span)
            })
            .collect()
    }

    fn index_parameters(&mut self) {
        for file in &self.source.files {
            for item in &file.outcome.ast.items {
                let Item::Definition(definition) = item else { continue };
                let Some(reference) = self.definition_at(definition.span) else { continue };
                let parameters = self.parameters(definition);
                match reference {
                    DefinitionRef::Function(id) => {
                        self.hir.functions[id.index].parameters = parameters
                    }
                    DefinitionRef::Template(id) => {
                        self.hir.templates[id.index].parameters = parameters
                    }
                    DefinitionRef::Bus(id) => self.hir.buses[id.index].parameters = parameters,
                }
            }
        }
    }

    fn index_ports(&mut self) {
        for file in &self.source.files {
            for item in &file.outcome.ast.items {
                let Item::Definition(definition) = item else { continue };
                let Some(reference) = self.definition_at(definition.span) else { continue };
                for statement in &definition.body.statements {
                    let Statement::Declaration(declaration) = statement else { continue };
                    let (kind, direction, tags, bus_type) = match &declaration.kind {
                        DeclarationKind::Signal { direction, tags } => {
                            (SymbolKind::Signal, Self::direction(*direction), tags.as_slice(), None)
                        }
                        DeclarationKind::Bus { direction, tags, .. } => {
                            (SymbolKind::Bus, Self::direction(*direction), tags.as_slice(), None)
                        }
                        DeclarationKind::Variable | DeclarationKind::Component => continue,
                    };
                    let visible = match reference {
                        DefinitionRef::Bus(_) => true,
                        DefinitionRef::Template(_) => direction.is_some(),
                        DefinitionRef::Function(_) => false,
                    };
                    if !visible {
                        continue;
                    }
                    let bus_type = match &declaration.kind {
                        DeclarationKind::Bus { type_name, .. } => Some(self.resolve_bus(type_name)),
                        _ => bus_type,
                    };
                    for declared in &declaration.symbols {
                        let symbol = self.hir.add_symbol(
                            declared.name.name.clone(),
                            kind,
                            declared.name.span,
                        );
                        self.hir.symbols[symbol.index].bus_type = bus_type.clone();
                        self.hir.symbols[symbol.index].rank = declared.dimensions.len();
                        let port = self.hir.add_port(symbol, direction, declared.span);
                        for tag in tags {
                            let tag_id =
                                self.hir.add_symbol(tag.name.clone(), SymbolKind::Tag, tag.span);
                            self.hir.symbols[symbol.index].tags.push(tag_id);
                            self.hir.ports[port.index].tags.push(tag_id);
                        }
                        self.predeclared_ports.insert(Self::span_key(declared.name.span), symbol);
                        match reference {
                            DefinitionRef::Template(id) => {
                                self.hir.templates[id.index].ports.push(port)
                            }
                            DefinitionRef::Bus(id) => self.hir.buses[id.index].ports.push(port),
                            DefinitionRef::Function(_) => {}
                        }
                    }
                }
            }
        }
    }

    fn definition_at(&self, span: Span) -> Option<DefinitionRef> {
        self.hir
            .functions
            .iter()
            .find(|item| item.span == span)
            .map(|item| DefinitionRef::Function(item.id))
            .or_else(|| {
                self.hir
                    .templates
                    .iter()
                    .find(|item| item.span == span)
                    .map(|item| DefinitionRef::Template(item.id))
            })
            .or_else(|| {
                self.hir
                    .buses
                    .iter()
                    .find(|item| item.span == span)
                    .map(|item| DefinitionRef::Bus(item.id))
            })
    }

    fn resolve_call(&mut self, name: &Identifier, expected: DefinitionKind) -> CallTarget {
        let definitions = self.hir.definitions_named(&name.name);
        let result = match definitions {
            [] => CallTarget::Missing {
                expected_kind: expected,
                name: name.name.clone(),
                span: name.span,
            },
            [actual] if Self::definition_kind(*actual) == expected => match actual {
                DefinitionRef::Function(id) => CallTarget::Function(*id),
                DefinitionRef::Template(id) => CallTarget::Template(*id),
                DefinitionRef::Bus(_) => {
                    CallTarget::WrongKind { expected_kind: expected, actual: *actual }
                }
            },
            [actual] => CallTarget::WrongKind { expected_kind: expected, actual: *actual },
            _ => CallTarget::Ambiguous {
                expected_kind: expected,
                name: name.name.clone(),
                span: name.span,
            },
        };
        match &result {
            CallTarget::Missing { .. } => {
                self.diagnostic(
                    SemanticCode::MissingCall,
                    Severity::Error,
                    name.span,
                    format!("unresolved {expected:?} call `{}`", name.name),
                );
                self.incomplete(name.span, IncompleteReason::MissingReference(name.name.clone()));
            }
            CallTarget::WrongKind { actual, .. } => {
                let code = if expected == DefinitionKind::Template {
                    SemanticCode::WrongTemplate
                } else {
                    SemanticCode::WrongFunction
                };
                self.diagnostics.push(SemanticDiagnostic {
                    code,
                    severity: Severity::Error,
                    span: name.span,
                    message: format!(
                        "`{}` is a {:?}, expected {expected:?}",
                        name.name,
                        Self::definition_kind(*actual)
                    ),
                    expected_kind: Some(expected),
                    actual_kind: Some(Self::definition_kind(*actual)),
                });
                self.incomplete(name.span, IncompleteReason::WrongKind(name.name.clone()));
            }
            CallTarget::Ambiguous { .. } => {
                self.incomplete(name.span, IncompleteReason::AmbiguousReference(name.name.clone()));
            }
            CallTarget::Function(_) | CallTarget::Template(_) | CallTarget::Opaque { .. } => {}
        }
        result
    }

    fn resolve_bus(&mut self, name: &Identifier) -> BusTarget {
        let definitions = self.hir.definitions_named(&name.name);
        let result = match definitions {
            [] => BusTarget::Missing { name: name.name.clone(), span: name.span },
            [DefinitionRef::Bus(id)] => BusTarget::Bus(*id),
            [actual] => BusTarget::WrongKind { actual: *actual, span: name.span },
            _ => BusTarget::Ambiguous { name: name.name.clone(), span: name.span },
        };
        match &result {
            BusTarget::Missing { .. } | BusTarget::WrongKind { .. } => {
                let actual_kind = match &result {
                    BusTarget::WrongKind { actual, .. } => Some(Self::definition_kind(*actual)),
                    _ => None,
                };
                let message = actual_kind.map_or_else(
                    || format!("unknown bus type `{}`", name.name),
                    |actual| format!("`{}` is a {actual:?}, expected Bus", name.name),
                );
                self.diagnostics.push(SemanticDiagnostic {
                    code: SemanticCode::MissingBusType,
                    severity: Severity::Error,
                    span: name.span,
                    message,
                    expected_kind: Some(DefinitionKind::Bus),
                    actual_kind,
                });
                self.incomplete(name.span, IncompleteReason::MissingReference(name.name.clone()));
            }
            BusTarget::Ambiguous { .. } => {
                self.incomplete(name.span, IncompleteReason::AmbiguousReference(name.name.clone()));
            }
            BusTarget::Bus(_) | BusTarget::Opaque { .. } => {}
        }
        result
    }

    fn check_arity(&mut self, target: &CallTarget, arguments: usize, span: Span) {
        let expected = match target {
            CallTarget::Function(id) => self.hir.function(*id).map(|item| item.parameters.len()),
            CallTarget::Template(id) => self.hir.template(*id).map(|item| item.parameters.len()),
            _ => None,
        };
        if let Some(expected) = expected {
            if arguments != expected {
                self.diagnostic(
                    SemanticCode::WrongArity,
                    Severity::Error,
                    span,
                    format!("expected {expected} arguments, found {arguments}"),
                );
                self.incomplete(span, IncompleteReason::Unsupported("wrong argument arity".into()));
            }
        }
    }

    fn lower_definitions(&mut self) {
        for kind in [DefinitionKind::Bus, DefinitionKind::Template, DefinitionKind::Function] {
            for file in &self.source.files {
                for item in &file.outcome.ast.items {
                    let Item::Definition(definition) = item else { continue };
                    let Some(reference) = self.definition_at(definition.span) else { continue };
                    if Self::definition_kind(reference) == kind {
                        self.lower_definition(definition, reference);
                    }
                }
            }
        }
    }

    fn lower_definition(&mut self, definition: &Definition, reference: DefinitionRef) {
        self.current_definition = Some(reference);
        self.scopes.enter();
        let parameters = match reference {
            DefinitionRef::Function(id) => self.hir.functions[id.index].parameters.clone(),
            DefinitionRef::Template(id) => self.hir.templates[id.index].parameters.clone(),
            DefinitionRef::Bus(id) => self.hir.buses[id.index].parameters.clone(),
        };
        for parameter in parameters {
            let name = self.hir.symbols[parameter.index].name.clone();
            if self.scopes.current(&name).is_none() {
                self.scopes.insert(name, parameter);
            }
        }
        let body = match reference {
            DefinitionRef::Function(id) => self.hir.functions[id.index].body,
            DefinitionRef::Template(id) => self.hir.templates[id.index].body,
            DefinitionRef::Bus(id) => self.hir.buses[id.index].body,
        };
        self.lower_block_into(&definition.body.statements, body, false);
        self.scopes.leave();
        self.current_definition = None;
    }

    fn lower_block_into(&mut self, statements: &[Statement], block: BlockId, scoped: bool) {
        if scoped {
            self.scopes.enter();
        }
        for statement in statements {
            let mut effects = self.lower_statement(statement);
            self.hir.blocks[block.index].effects.append(&mut effects);
        }
        if scoped {
            self.scopes.leave();
        }
    }

    fn lower_branch(&mut self, statement: &Statement) -> BlockId {
        let block = self.hir.add_block(statement.span());
        match statement {
            Statement::Block(body) => self.lower_block_into(&body.statements, block, true),
            _ => self.lower_block_into(std::slice::from_ref(statement), block, true),
        }
        block
    }

    fn lower_statement(&mut self, statement: &Statement) -> Vec<Effect> {
        let span = statement.span();
        match statement {
            Statement::Block(_) => vec![Effect::Block(self.lower_branch(statement))],
            Statement::Declaration(declaration) => self.lower_declaration(declaration),
            Statement::Assignment { target, operator, value, .. } => {
                vec![self.lower_assignment(target, *operator, value, span)]
            }
            Statement::PostfixUpdate { target, operator, .. } => {
                let Some(path) = self.lower_access(target) else {
                    return vec![self.opaque(span, IncompleteReason::InvalidAssignment)];
                };
                if self.hir.symbols[path.root.index].kind != SymbolKind::Variable {
                    return vec![
                        self.invalid_assignment(span, "postfix update requires a variable")
                    ];
                }
                vec![Effect::Update { target: path, operator: *operator, span }]
            }
            Statement::Constraint { left, right, .. } => {
                let left = self.lower_expression(left);
                let right = self.lower_expression(right);
                vec![Effect::EqualityConstraint { left, right, span }]
            }
            Statement::If { condition, then_branch, else_branch, .. } => {
                let condition = self.lower_expression(condition);
                let then_block = self.lower_branch(then_branch);
                let else_block = else_branch.as_ref().map(|branch| self.lower_branch(branch));
                vec![Effect::If { condition, then_block, else_block, span }]
            }
            Statement::For { initializer, condition, step, body, .. } => {
                self.scopes.enter();
                let initializer_block = self.hir.add_block(initializer.span());
                self.lower_block_into(std::slice::from_ref(initializer), initializer_block, false);
                let condition = self.lower_expression(condition);
                let step = self.lower_branch(step);
                let body = self.lower_branch(body);
                self.scopes.leave();
                vec![Effect::For { initializer: initializer_block, condition, step, body, span }]
            }
            Statement::While { condition, body, .. } => {
                let condition = self.lower_expression(condition);
                let body = self.lower_branch(body);
                vec![Effect::While { condition, body, span }]
            }
            Statement::Return { value, .. } => {
                vec![Effect::Return { value: self.lower_expression(value), span }]
            }
            Statement::Assert { condition, .. } => {
                vec![Effect::Assert { condition: self.lower_expression(condition), span }]
            }
            Statement::Log { arguments, .. } => {
                let values = arguments
                    .iter()
                    .filter_map(|argument| match argument {
                        LogArgument::String { .. } => None,
                        LogArgument::Expression(value) => Some(self.lower_expression(value)),
                    })
                    .collect();
                vec![Effect::Log { values, span }]
            }
            Statement::AnonymousCall { call, .. } => {
                let expression = self.lower_anonymous(call);
                vec![Effect::AnonymousComponent { expression, span }]
            }
            Statement::Error { .. } => vec![self.opaque(span, IncompleteReason::Syntax)],
        }
    }

    fn opaque(&mut self, span: Span, reason: IncompleteReason) -> Effect {
        self.incomplete(span, reason.clone());
        Effect::Opaque { reason, span }
    }

    fn invalid_assignment(&mut self, span: Span, message: &str) -> Effect {
        self.diagnostic(SemanticCode::InvalidAssignment, Severity::Error, span, message.into());
        self.opaque(span, IncompleteReason::InvalidAssignment)
    }

    fn declare(&mut self, name: &Identifier, kind: SymbolKind) -> SymbolId {
        if self.scopes.current(&name.name).is_some() {
            self.diagnostic(
                SemanticCode::DuplicateSymbol,
                Severity::Error,
                name.span,
                format!("duplicate local symbol `{}`", name.name),
            );
            self.incomplete(name.span, IncompleteReason::AmbiguousReference(name.name.clone()));
        } else if let Some(outer) = self.scopes.outer(&name.name) {
            if kind == SymbolKind::Variable
                && self.hir.symbols[outer.index].kind == SymbolKind::Variable
            {
                self.diagnostic(
                    SemanticCode::Shadowing,
                    Severity::Warning,
                    name.span,
                    format!("variable `{}` shadows an outer declaration", name.name),
                );
            }
        }
        let id = self.hir.add_symbol(name.name.clone(), kind, name.span);
        if self.scopes.current(&name.name).is_none() {
            self.scopes.insert(name.name.clone(), id);
        }
        id
    }

    fn lower_declaration(&mut self, declaration: &Declaration) -> Vec<Effect> {
        let kind = match declaration.kind {
            DeclarationKind::Variable => SymbolKind::Variable,
            DeclarationKind::Component => SymbolKind::Component,
            DeclarationKind::Signal { .. } => SymbolKind::Signal,
            DeclarationKind::Bus { .. } => SymbolKind::Bus,
        };
        let tags = match &declaration.kind {
            DeclarationKind::Signal { tags, .. } | DeclarationKind::Bus { tags, .. } => {
                tags.as_slice()
            }
            DeclarationKind::Variable | DeclarationKind::Component => &[],
        };
        let bus_arguments: Vec<_> = match &declaration.kind {
            DeclarationKind::Bus { arguments, .. } => arguments
                .values()
                .iter()
                .map(|argument| {
                    let id = self.lower_expression(argument);
                    self.expect_compile_time(id, argument.span(), false);
                    id
                })
                .collect(),
            _ => Vec::new(),
        };
        let bus_type = match &declaration.kind {
            DeclarationKind::Bus { type_name, .. } => {
                let predeclared = declaration.symbols.first().and_then(|declared| {
                    self.predeclared_ports.get(&Self::span_key(declared.name.span)).copied()
                });
                if let Some(symbol) = predeclared {
                    self.hir.symbols[symbol.index].bus_type.clone()
                } else {
                    Some(self.resolve_bus(type_name))
                }
            }
            _ => None,
        };
        if let Some(BusTarget::Bus(id)) = bus_type {
            let expected = self.hir.buses[id.index].parameters.len();
            if expected != bus_arguments.len() {
                self.diagnostic(
                    SemanticCode::WrongArity,
                    Severity::Error,
                    declaration.span,
                    format!("bus expects {expected} arguments, found {}", bus_arguments.len()),
                );
                self.incomplete(
                    declaration.span,
                    IncompleteReason::Unsupported("wrong bus argument arity".into()),
                );
            }
        }
        let mut effects = Vec::new();
        for declared in &declaration.symbols {
            let symbol = if let Some(symbol) =
                self.predeclared_ports.get(&Self::span_key(declared.name.span)).copied()
            {
                self.bind_predeclared(&declared.name, symbol);
                symbol
            } else {
                self.declare(&declared.name, kind)
            };
            self.hir.symbols[symbol.index].bus_type = bus_type.clone();
            self.hir.symbols[symbol.index].bus_arguments = bus_arguments.clone();
            self.hir.symbols[symbol.index].rank = declared.dimensions.len();
            for dimension in &declared.dimensions {
                let id = self.lower_expression(dimension);
                self.expect_compile_time(id, dimension.span(), true);
                self.hir.symbols[symbol.index].dimensions.push(id);
            }
            if kind == SymbolKind::Component {
                self.components.insert(symbol, self.hir.add_component(symbol, declared.span));
            }
            if self.hir.symbols[symbol.index].tags.is_empty() {
                for tag in tags {
                    let id = self.hir.add_symbol(tag.name.clone(), SymbolKind::Tag, tag.span);
                    self.hir.symbols[symbol.index].tags.push(id);
                }
            }
            effects.push(Effect::Declaration { symbol, span: declared.span });
            if let Some((operator, value)) = &declared.initialization {
                effects.push(self.assignment_for_symbol(symbol, *operator, value, declared.span));
            }
        }
        if let Some((operator, value)) = &declaration.tuple_initialization {
            if let Expression::Tuple { elements, .. } = value {
                if elements.len() == declaration.symbols.len() {
                    for (declared, element) in declaration.symbols.iter().zip(elements) {
                        if let Some(symbol) = self.scopes.resolve(&declared.name.name) {
                            effects.push(self.assignment_for_symbol(
                                symbol,
                                *operator,
                                element,
                                declared.span,
                            ));
                        }
                    }
                } else {
                    effects.push(self.invalid_assignment(
                        declaration.span,
                        "tuple initializer has the wrong number of elements",
                    ));
                }
            } else {
                effects.push(self.opaque(
                    declaration.span,
                    IncompleteReason::Unsupported("nonliteral tuple initializer".into()),
                ));
            }
        }
        effects
    }

    fn bind_predeclared(&mut self, name: &Identifier, symbol: SymbolId) {
        if self.scopes.current(&name.name).is_some() {
            self.diagnostic(
                SemanticCode::DuplicateSymbol,
                Severity::Error,
                name.span,
                format!("duplicate local symbol `{}`", name.name),
            );
        } else {
            self.scopes.insert(name.name.clone(), symbol);
        }
    }

    fn direction(direction: DirectionSyntax) -> Option<PortDirection> {
        match direction {
            DirectionSyntax::Unspecified => None,
            DirectionSyntax::Before(value) | DirectionSyntax::After(value) => Some(value.direction),
        }
    }

    fn assignment_for_symbol(
        &mut self,
        symbol: SymbolId,
        operator: AssignmentOperator,
        value: &Expression,
        span: Span,
    ) -> Effect {
        let path = AccessPath {
            root: symbol,
            steps: Vec::new(),
            terminal: symbol,
            component_input: false,
            component_output: false,
            span,
        };
        let kind = self.hir.symbols[symbol.index].kind;
        let value = if kind == SymbolKind::Component {
            self.lower_component_value(symbol, value)
        } else {
            self.lower_expression(value)
        };
        self.assignment_effect(path, kind, operator, value, span)
    }

    fn lower_assignment(
        &mut self,
        target: &Expression,
        operator: AssignmentOperator,
        value: &Expression,
        span: Span,
    ) -> Effect {
        let Some(path) = self.lower_access(target) else {
            return self.invalid_assignment(span, "invalid assignment target");
        };
        let kind = self.hir.symbols[path.terminal.index].kind;
        let value = if kind == SymbolKind::Component {
            self.lower_component_value(path.root, value)
        } else {
            self.lower_expression(value)
        };
        if path.component_output {
            return self.invalid_assignment(span, "cannot assign a component output port");
        }
        self.assignment_effect(path, kind, operator, value, span)
    }

    fn assignment_effect(
        &mut self,
        path: AccessPath,
        kind: SymbolKind,
        operator: AssignmentOperator,
        value: ExprId,
        span: Span,
    ) -> Effect {
        match (kind, operator) {
            (SymbolKind::Variable, AssignmentOperator::Assign)
            | (SymbolKind::Variable, AssignmentOperator::Add)
            | (SymbolKind::Variable, AssignmentOperator::Subtract)
            | (SymbolKind::Variable, AssignmentOperator::Multiply)
            | (SymbolKind::Variable, AssignmentOperator::Divide)
            | (SymbolKind::Variable, AssignmentOperator::IntegerDivide)
            | (SymbolKind::Variable, AssignmentOperator::Modulo)
            | (SymbolKind::Variable, AssignmentOperator::Power)
            | (SymbolKind::Variable, AssignmentOperator::ShiftLeft)
            | (SymbolKind::Variable, AssignmentOperator::ShiftRight)
            | (SymbolKind::Variable, AssignmentOperator::BitAnd)
            | (SymbolKind::Variable, AssignmentOperator::BitOr)
            | (SymbolKind::Variable, AssignmentOperator::BitXor)
            | (SymbolKind::Component, AssignmentOperator::Assign)
            | (SymbolKind::Tag, AssignmentOperator::Assign) => {
                if matches!(kind, SymbolKind::Variable | SymbolKind::Tag) {
                    let current = self.hir.symbols[path.terminal.index].knownness;
                    let next = self.knownness(value);
                    self.hir.symbols[path.terminal.index].knownness =
                        if operator == AssignmentOperator::Assign {
                            next
                        } else {
                            current.join(next)
                        };
                }
                if kind == SymbolKind::Component
                    && self.expression_type(value) == ValueType::Unknown
                {
                    return self.opaque(span, IncompleteReason::InvalidAssignment);
                }
                Effect::CompileTimeAssignment { target: path, value, span }
            }
            (
                SymbolKind::Signal | SymbolKind::Bus,
                AssignmentOperator::Witness | AssignmentOperator::ReverseWitness,
            ) => Effect::WitnessAssignment { target: path, value, span },
            (
                SymbolKind::Signal | SymbolKind::Bus,
                AssignmentOperator::Constraint | AssignmentOperator::ReverseConstraint,
            ) => Effect::ConstraintAssignment { target: path, value, span },
            _ => self.invalid_assignment(span, "assignment operator is invalid for target kind"),
        }
    }

    fn lower_component_value(&mut self, symbol: SymbolId, value: &Expression) -> ExprId {
        let call = match value {
            Expression::Call { name, arguments, span } => Some((name, arguments.as_slice(), *span)),
            Expression::Parallel { operand, .. } => match operand.as_ref() {
                Expression::Call { name, arguments, span } => {
                    Some((name, arguments.as_slice(), *span))
                }
                _ => None,
            },
            _ => None,
        };
        let Some((name, arguments, span)) = call else {
            self.diagnostic(
                SemanticCode::InvalidAssignment,
                Severity::Error,
                value.span(),
                "component requires a template call".into(),
            );
            self.incomplete(value.span(), IncompleteReason::InvalidAssignment);
            return self.add_expression(
                ExprKind::Opaque(IncompleteReason::InvalidAssignment),
                Knownness::Opaque,
                value.span(),
                ValueType::Unknown,
            );
        };
        let arguments: Vec<_> =
            arguments.iter().map(|value| self.lower_expression(value)).collect();
        let target = self.resolve_call(name, DefinitionKind::Template);
        self.check_arity(&target, arguments.len(), span);
        if let Some(component) = self.components.get(&symbol) {
            self.hir.components[component.index].target = Some(target.clone());
        }
        let ty = match target {
            CallTarget::Template(id) => ValueType::Component(id),
            _ => ValueType::Unknown,
        };
        self.add_expression(ExprKind::Call { target, arguments }, Knownness::Opaque, span, ty)
    }

    fn lower_access(&mut self, expression: &Expression) -> Option<AccessPath> {
        let Expression::Name { identifier, access, span } = expression else { return None };
        let Some(root) = self.scopes.resolve(&identifier.name) else {
            self.diagnostic(
                SemanticCode::UnknownSymbol,
                Severity::Error,
                identifier.span,
                format!("unknown symbol `{}`", identifier.name),
            );
            self.incomplete(
                identifier.span,
                IncompleteReason::UnknownSymbol(identifier.name.clone()),
            );
            return None;
        };
        let mut ty = self.symbol_type(root);
        let mut terminal = root;
        let mut remaining_dimensions = self.hir.symbols[root.index].rank;
        let mut external_input = false;
        let mut external_output = false;
        let mut steps = Vec::new();
        for part in access {
            match part {
                Access::Index { expression, span } => {
                    if remaining_dimensions == 0 {
                        self.diagnostic(
                            SemanticCode::InvalidArrayAccess,
                            Severity::Error,
                            *span,
                            "index applied to a scalar or beyond declared array rank".into(),
                        );
                        self.incomplete(*span, IncompleteReason::InvalidAssignment);
                        return None;
                    }
                    let id = self.lower_expression(expression);
                    let index = match &self.hir.expressions[id.index].kind {
                        ExprKind::Number(value) => ArrayIndex::Constant(value.clone()),
                        _ => ArrayIndex::Symbolic(id),
                    };
                    steps.push(AccessStep::Index { index, span: *span });
                    remaining_dimensions = remaining_dimensions.saturating_sub(1);
                }
                Access::Field { field, span } => {
                    if remaining_dimensions != 0 {
                        self.diagnostic(
                            SemanticCode::InvalidArrayAccess,
                            Severity::Error,
                            *span,
                            "field access requires a fully indexed array".into(),
                        );
                        self.incomplete(*span, IncompleteReason::InvalidAssignment);
                        return None;
                    }
                    let from_component = matches!(ty, ValueType::Component(_));
                    let (step, symbol, next) = self.resolve_field(
                        ty,
                        terminal,
                        field,
                        remaining_dimensions,
                        external_input,
                    )?;
                    if from_component {
                        if let AccessStep::Port { port, .. } = &step {
                            external_input |=
                                self.hir.ports[port.index].direction == Some(PortDirection::Input);
                            external_output |=
                                self.hir.ports[port.index].direction == Some(PortDirection::Output);
                        }
                    }
                    steps.push(match step {
                        AccessStep::Port { port, .. } => AccessStep::Port { port, span: *span },
                        AccessStep::Tag { symbol, .. } => AccessStep::Tag { symbol, span: *span },
                        AccessStep::Index { .. } => return None,
                    });
                    terminal = symbol;
                    ty = next;
                    remaining_dimensions = self.hir.symbols[terminal.index].rank;
                }
            }
        }
        Some(AccessPath {
            root,
            steps,
            terminal,
            component_input: external_input,
            component_output: external_output,
            span: *span,
        })
    }

    fn symbol_type(&self, symbol: SymbolId) -> ValueType {
        let info = &self.hir.symbols[symbol.index];
        match info.kind {
            SymbolKind::Bus => match &info.bus_type {
                Some(BusTarget::Bus(id)) => ValueType::Bus(*id),
                _ => ValueType::Unknown,
            },
            SymbolKind::Component => self
                .components
                .get(&symbol)
                .and_then(|id| self.hir.components[id.index].target.as_ref())
                .map_or(ValueType::Unknown, |target| match target {
                    CallTarget::Template(id) => ValueType::Component(*id),
                    _ => ValueType::Unknown,
                }),
            SymbolKind::Parameter => ValueType::Unknown,
            _ => ValueType::Plain,
        }
    }

    fn resolve_field(
        &mut self,
        ty: ValueType,
        current: SymbolId,
        field: &Identifier,
        remaining_dimensions: usize,
        external_input: bool,
    ) -> Option<(AccessStep, SymbolId, ValueType)> {
        let tag = self.hir.symbols[current.index]
            .tags
            .iter()
            .find(|tag| self.hir.symbols[tag.index].name == field.name)
            .copied();
        if let Some(symbol) = tag {
            if remaining_dimensions != 0 || external_input {
                self.diagnostic(
                    SemanticCode::InvalidSignalAccess,
                    Severity::Error,
                    field.span,
                    format!("tag `{}` cannot be accessed here", field.name),
                );
                self.incomplete(field.span, IncompleteReason::InvalidAssignment);
                return None;
            }
            return Some((AccessStep::Tag { symbol, span: field.span }, symbol, ValueType::Plain));
        }
        let ports = match ty {
            ValueType::Bus(id) => Some(self.hir.buses[id.index].ports.as_slice()),
            ValueType::Component(id) => Some(self.hir.templates[id.index].ports.as_slice()),
            ValueType::Plain | ValueType::Unknown => None,
        };
        if let Some(ports) = ports {
            let result = ports
                .iter()
                .find(|port| {
                    self.hir.symbols[self.hir.ports[port.index].symbol.index].name == field.name
                })
                .copied();
            if let Some(port) = result {
                let symbol = self.hir.ports[port.index].symbol;
                return Some((
                    AccessStep::Port { port, span: field.span },
                    symbol,
                    self.symbol_type(symbol),
                ));
            }
            self.diagnostic(
                SemanticCode::InvalidSignalAccess,
                Severity::Error,
                field.span,
                format!("unknown field `{}`", field.name),
            );
            self.incomplete(field.span, IncompleteReason::UnknownSymbol(field.name.clone()));
        } else if ty == ValueType::Unknown {
            self.incomplete(field.span, IncompleteReason::UnknownType);
        } else {
            self.diagnostic(
                SemanticCode::InvalidSignalAccess,
                Severity::Error,
                field.span,
                format!("`{}` is not a declared field or tag", field.name),
            );
            self.incomplete(field.span, IncompleteReason::UnknownSymbol(field.name.clone()));
        }
        None
    }

    fn lower_expression(&mut self, expression: &Expression) -> ExprId {
        let span = expression.span();
        match expression {
            Expression::Number { text, .. } => self.add_expression(
                ExprKind::Number(text.clone()),
                Knownness::Constant,
                span,
                ValueType::Plain,
            ),
            Expression::Name { .. } => {
                let Some(path) = self.lower_access(expression) else {
                    return self.add_expression(
                        ExprKind::Opaque(IncompleteReason::UnknownType),
                        Knownness::Opaque,
                        span,
                        ValueType::Unknown,
                    );
                };
                let ty = self.access_type(&path);
                let knownness = self.hir.symbols[path.terminal.index].knownness;
                if knownness == Knownness::Opaque {
                    self.incomplete(span, IncompleteReason::UnknownType);
                }
                self.add_expression(ExprKind::Access(path), knownness, span, ty)
            }
            Expression::Call { name, arguments, .. } => {
                let arguments: Vec<_> =
                    arguments.iter().map(|value| self.lower_expression(value)).collect();
                let target = self.resolve_call(name, DefinitionKind::Function);
                self.check_arity(&target, arguments.len(), span);
                let knownness = if matches!(target, CallTarget::Function(_))
                    && arguments.iter().all(|id| self.knownness(*id).is_compile_time())
                {
                    Knownness::ParameterDependent
                } else {
                    Knownness::Opaque
                };
                self.add_expression(
                    ExprKind::Call { target, arguments },
                    knownness,
                    span,
                    ValueType::Plain,
                )
            }
            Expression::AnonymousCall(call) => self.lower_anonymous(call),
            Expression::Array { elements, .. } | Expression::Tuple { elements, .. } => {
                let elements: Vec<_> =
                    elements.iter().map(|value| self.lower_expression(value)).collect();
                let knownness = elements
                    .iter()
                    .fold(Knownness::Constant, |acc, id| acc.join(self.knownness(*id)));
                let ty = self.array_type(&elements);
                if matches!(expression, Expression::Array { .. }) {
                    self.array_types.insert(Self::span_key(span), ty);
                    self.add_expression(ExprKind::Array(elements), knownness, span, ty)
                } else {
                    self.add_expression(ExprKind::Tuple(elements), knownness, span, ty)
                }
            }
            Expression::Unary { operator, operand, .. } => {
                let operand = self.lower_expression(operand);
                self.add_expression(
                    ExprKind::Unary { operator: *operator, operand },
                    self.knownness(operand),
                    span,
                    ValueType::Plain,
                )
            }
            Expression::Binary { operator, left, right, .. } => {
                let left = self.lower_expression(left);
                let right = self.lower_expression(right);
                let knownness = self.knownness(left).join(self.knownness(right));
                self.add_expression(
                    ExprKind::Binary { operator: *operator, left, right },
                    knownness,
                    span,
                    ValueType::Plain,
                )
            }
            Expression::Ternary { condition, yes, no, .. } => {
                let condition = self.lower_expression(condition);
                let yes = self.lower_expression(yes);
                let no = self.lower_expression(no);
                let knownness =
                    self.knownness(condition).join(self.knownness(yes)).join(self.knownness(no));
                let ty = if self.expression_type(yes) == self.expression_type(no) {
                    self.expression_type(yes)
                } else {
                    ValueType::Unknown
                };
                self.add_expression(ExprKind::Ternary { condition, yes, no }, knownness, span, ty)
            }
            Expression::Parallel { operand, .. } => {
                let operand = self.lower_expression(operand);
                self.add_expression(
                    ExprKind::Parallel(operand),
                    Knownness::Opaque,
                    span,
                    self.expression_type(operand),
                )
            }
            Expression::Group { expression, .. } => self.lower_expression(expression),
            Expression::Error { .. } => {
                self.incomplete(span, IncompleteReason::Syntax);
                self.add_expression(
                    ExprKind::Opaque(IncompleteReason::Syntax),
                    Knownness::Opaque,
                    span,
                    ValueType::Unknown,
                )
            }
        }
    }

    fn access_type(&self, path: &AccessPath) -> ValueType {
        self.symbol_type(path.terminal)
    }

    fn array_type(&self, elements: &[ExprId]) -> ValueType {
        if elements.is_empty() {
            return ValueType::Plain;
        }
        let mut ty = ValueType::Plain;
        for element in elements {
            match self.expression_type(*element) {
                ValueType::Bus(id) => ty = ValueType::Bus(id),
                ValueType::Component(_) => return ValueType::Unknown,
                ValueType::Unknown if !matches!(ty, ValueType::Bus(_)) => ty = ValueType::Unknown,
                _ => {}
            }
        }
        ty
    }

    fn span_key(span: Span) -> (usize, usize, usize) {
        (span.source().index(), span.start(), span.end())
    }

    fn lower_anonymous(&mut self, call: &AnonymousCallExpr) -> ExprId {
        let target = self.resolve_call(&call.name, DefinitionKind::Template);
        let arguments: Vec<_> =
            call.parameters.iter().map(|value| self.lower_expression(value)).collect();
        self.check_arity(&target, arguments.len(), call.span);
        let template = if let CallTarget::Template(id) = target { Some(id) } else { None };
        let inputs: Vec<_> = call
            .inputs
            .iter()
            .enumerate()
            .map(|(position, input)| self.lower_anonymous_input(template, input, position))
            .collect();
        let symbol = self.hir.add_symbol(
            format!("<anonymous:{}>", call.span.start()),
            SymbolKind::Component,
            call.span,
        );
        let component = self.hir.add_component(symbol, call.span);
        self.hir.components[component.index].target = Some(target);
        self.add_expression(
            ExprKind::AnonymousComponent { component, arguments, inputs },
            Knownness::WitnessDependent,
            call.span,
            ValueType::Unknown,
        )
    }

    fn lower_anonymous_input(
        &mut self,
        template: Option<TemplateId>,
        input: &AnonymousInput,
        position: usize,
    ) -> AnonymousInputEffect {
        let (name, operator, value, span) = match input {
            AnonymousInput::Positional(value) => {
                (None, InputAssignmentOperator::Constraint, value, value.span())
            }
            AnonymousInput::Named { name, operator, value, span } => {
                (Some(name), *operator, value, *span)
            }
        };
        let value = self.lower_expression(value);
        let port = template.and_then(|id| {
            let inputs = self.hir.templates[id.index]
                .ports
                .iter()
                .filter(|port| self.hir.ports[port.index].direction == Some(PortDirection::Input));
            if let Some(name) = name {
                inputs
                    .into_iter()
                    .find(|port| {
                        self.hir.symbols[self.hir.ports[port.index].symbol.index].name == name.name
                    })
                    .copied()
            } else {
                inputs.into_iter().nth(position).copied()
            }
        });
        let target = if operator != InputAssignmentOperator::Constraint {
            self.diagnostic(
                SemanticCode::AnonymousInput,
                Severity::Error,
                span,
                "anonymous input requires `<==`".into(),
            );
            self.incomplete(span, IncompleteReason::InvalidAssignment);
            AnonymousInputTarget::Opaque(IncompleteReason::InvalidAssignment)
        } else if let Some(port) = port {
            AnonymousInputTarget::Port(port)
        } else {
            self.diagnostic(
                SemanticCode::AnonymousInput,
                Severity::Error,
                span,
                "anonymous input does not name an input port".into(),
            );
            let reason = IncompleteReason::UnknownSymbol(
                name.map_or_else(|| position.to_string(), |name| name.name.clone()),
            );
            self.incomplete(span, reason.clone());
            AnonymousInputTarget::Opaque(reason)
        };
        AnonymousInputEffect { target, operator, value, span }
    }

    fn lower_mains(&mut self) {
        for file in &self.source.files {
            for item in &file.outcome.ast.items {
                let Item::Main { instance, span, .. } = item else { continue };
                let call = match instance {
                    Expression::Call { name, arguments, .. } => Some((name, arguments.as_slice())),
                    Expression::Parallel { operand, .. } => match operand.as_ref() {
                        Expression::Call { name, arguments, .. } => {
                            Some((name, arguments.as_slice()))
                        }
                        _ => None,
                    },
                    _ => None,
                };
                if let Some((name, arguments)) = call {
                    self.scopes.enter();
                    let arguments: Vec<_> =
                        arguments.iter().map(|value| self.lower_expression(value)).collect();
                    self.scopes.leave();
                    let target = self.resolve_call(name, DefinitionKind::Template);
                    self.check_arity(&target, arguments.len(), *span);
                    self.hir.mains.push(Main { target, arguments, span: *span });
                } else {
                    self.diagnostic(
                        SemanticCode::WrongTemplate,
                        Severity::Error,
                        *span,
                        "main requires a template call".into(),
                    );
                    self.incomplete(*span, IncompleteReason::Unsupported("main expression".into()));
                }
            }
        }
    }

    fn resolve_pending_features(&mut self) {
        for file in &self.source.files {
            for check in &file.outcome.pending_feature_checks {
                let ty = self.array_types.get(&Self::span_key(check.span)).copied();
                match ty {
                    Some(ValueType::Bus(_)) => self.diagnostic(
                        SemanticCode::FeatureVersion,
                        Severity::Error,
                        check.span,
                        format!(
                            "bus-valued inline array requires Circom {}.{}.{}",
                            check.required_version.major,
                            check.required_version.minor,
                            check.required_version.patch
                        ),
                    ),
                    Some(ValueType::Plain) => {}
                    Some(ValueType::Component(_)) | Some(ValueType::Unknown) | None => {
                        self.incomplete(check.span, IncompleteReason::UnknownType);
                    }
                }
            }
        }
    }

    fn collect_syntax_incomplete(&mut self) {
        for diagnostic in &self.source.diagnostics {
            let Some(span) = diagnostic.span() else { continue };
            let reason = match diagnostic.kind {
                DiagnosticKind::MissingInclude
                | DiagnosticKind::FileRead
                | DiagnosticKind::CyclicInclude => IncompleteReason::Include,
                _ => IncompleteReason::Syntax,
            };
            self.incomplete(span, reason);
        }
    }
}

/// Lowers all available definitions after indexing names across every loaded source file.
#[must_use]
pub fn lower_project(source: &LoadedProject) -> LoweredProject {
    let mut lowerer = Lowerer {
        source,
        hir: HirProject::new(),
        diagnostics: Vec::new(),
        incomplete: Vec::new(),
        expression_types: Vec::new(),
        array_types: BTreeMap::new(),
        components: BTreeMap::new(),
        predeclared_ports: BTreeMap::new(),
        scopes: Scopes::default(),
        current_definition: None,
    };
    lowerer.index_definitions();
    lowerer.index_parameters();
    lowerer.index_ports();
    lowerer.lower_definitions();
    lowerer.lower_mains();
    lowerer.resolve_pending_features();
    lowerer.collect_syntax_incomplete();
    lowerer.diagnostics.sort_by_key(|diagnostic| {
        (diagnostic.span.source().index(), diagnostic.span.start(), diagnostic.span.end())
    });
    lowerer.incomplete.sort_by_key(|region| {
        (region.span.source().index(), region.span.start(), region.span.end())
    });
    LoweredProject {
        hir: lowerer.hir,
        diagnostics: lowerer.diagnostics,
        syntax_diagnostics: source.diagnostics.clone(),
        incomplete: lowerer.incomplete,
    }
}
