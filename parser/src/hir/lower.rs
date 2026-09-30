use std::collections::{BTreeMap, BTreeSet};

use super::{
    AccessPath, AccessStep, AnonymousInputEffect, AnonymousInputTarget, ArrayIndex, BlockId, Bus,
    BusId, BusTarget, CallTarget, ComponentId, DefinitionKind, DefinitionRef, Effect, ExprId,
    ExprKind, HirProject, IncompleteLocation, IncompleteReason, IncompleteRegion, Knownness,
    LoweredProject, Main, SemanticCode, SemanticDiagnostic, Severity, SymbolId, SymbolKind,
    Template, TemplateId, Function, FunctionId,
};
use crate::new_frontend::{
    Access, AnonymousCallExpr, AnonymousInput, AssignmentOperator, Declaration, DeclarationKind,
    DeclaredSymbol, Definition, DefinitionKind as SourceDefinitionKind, DirectionSyntax,
    Expression, Identifier, Item, LoadedProject, LogArgument, PortDirection, Span, Statement,
    DiagnosticKind, InputAssignmentOperator,
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

struct AccessState {
    ty: ValueType,
    terminal: SymbolId,
    remaining_dimensions: usize,
    component_input: bool,
    component_output: bool,
    indexed_current: bool,
    steps: Vec<AccessStep>,
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
    definition_locations: BTreeMap<(usize, usize, usize), DefinitionRef>,
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
        self.incomplete
            .push(IncompleteRegion { location: IncompleteLocation::Source(span), reason });
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
                            name_span: definition.name.span,
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
                            name_span: definition.name.span,
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
                            name_span: definition.name.span,
                        });
                        DefinitionRef::Bus(id)
                    }
                };
                self.hir.definitions.entry(name).or_default().push(reference);
                self.definition_locations.insert(Self::span_key(definition.span), reference);
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
            DefinitionRef::Function(id) => self.hir.functions[id.index].name_span,
            DefinitionRef::Template(id) => self.hir.templates[id.index].name_span,
            DefinitionRef::Bus(id) => self.hir.buses[id.index].name_span,
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
                let mut known_parameters: BTreeSet<String> = match reference {
                    DefinitionRef::Function(id) => &self.hir.functions[id.index].parameters,
                    DefinitionRef::Template(id) => &self.hir.templates[id.index].parameters,
                    DefinitionRef::Bus(id) => &self.hir.buses[id.index].parameters,
                }
                .iter()
                .map(|id| self.hir.symbols[id.index].name.clone())
                .collect();
                for statement in &definition.body.statements {
                    let Statement::Declaration(declaration) = statement else {
                        known_parameters.clear();
                        continue;
                    };
                    let (kind, direction, tags, bus_type) = match &declaration.kind {
                        DeclarationKind::Signal { direction, tags } => {
                            (SymbolKind::Signal, Self::direction(*direction), tags.as_slice(), None)
                        }
                        DeclarationKind::Bus { direction, tags, .. } => {
                            (SymbolKind::Bus, Self::direction(*direction), tags.as_slice(), None)
                        }
                        DeclarationKind::Variable | DeclarationKind::Component => {
                            Self::remove_shadowed_parameters(&mut known_parameters, declaration);
                            continue;
                        }
                    };
                    let visible = match reference {
                        DefinitionRef::Bus(_) => true,
                        DefinitionRef::Template(_) => direction.is_some(),
                        DefinitionRef::Function(_) => false,
                    };
                    if !visible {
                        Self::remove_shadowed_parameters(&mut known_parameters, declaration);
                        continue;
                    }
                    let bus_type = match &declaration.kind {
                        DeclarationKind::Bus { type_name, arguments, .. } => {
                            Some(self.preindex_bus_type(
                                type_name,
                                arguments.values(),
                                &known_parameters,
                                declaration.span,
                            ))
                        }
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
                    Self::remove_shadowed_parameters(&mut known_parameters, declaration);
                }
            }
        }
    }

    fn remove_shadowed_parameters(names: &mut BTreeSet<String>, declaration: &Declaration) {
        for symbol in &declaration.symbols {
            names.remove(&symbol.name.name);
        }
    }

    fn preindex_bus_type(
        &mut self,
        name: &Identifier,
        arguments: &[Expression],
        parameters: &BTreeSet<String>,
        span: Span,
    ) -> BusTarget {
        let target = self.resolve_bus(name);
        let BusTarget::Bus(id) = target else { return target };
        let expected = self.hir.buses[id.index].parameters.len();
        if expected != arguments.len() {
            self.diagnostic(
                SemanticCode::WrongArity,
                Severity::Error,
                span,
                format!("bus expects {expected} arguments, found {}", arguments.len()),
            );
            self.incomplete(span, IncompleteReason::Unsupported("wrong bus argument arity".into()));
            return BusTarget::Opaque {
                reason: IncompleteReason::Unsupported("wrong bus argument arity".into()),
            };
        }
        if arguments.iter().all(|argument| Self::syntactic_compile_time(argument, parameters)) {
            BusTarget::Bus(id)
        } else {
            BusTarget::Opaque { reason: IncompleteReason::UnknownType }
        }
    }

    fn syntactic_compile_time(expression: &Expression, parameters: &BTreeSet<String>) -> bool {
        match expression {
            Expression::Number { .. } => true,
            Expression::Name { identifier, access, .. } => {
                access.is_empty() && parameters.contains(&identifier.name)
            }
            Expression::Unary { operand, .. } | Expression::Group { expression: operand, .. } => {
                Self::syntactic_compile_time(operand, parameters)
            }
            Expression::Binary { left, right, .. } => {
                Self::syntactic_compile_time(left, parameters)
                    && Self::syntactic_compile_time(right, parameters)
            }
            Expression::Ternary { condition, yes, no, .. } => {
                Self::syntactic_compile_time(condition, parameters)
                    && Self::syntactic_compile_time(yes, parameters)
                    && Self::syntactic_compile_time(no, parameters)
            }
            Expression::Array { elements, .. } | Expression::Tuple { elements, .. } => {
                elements.iter().all(|element| Self::syntactic_compile_time(element, parameters))
            }
            Expression::Call { .. }
            | Expression::AnonymousCall(_)
            | Expression::Parallel { .. }
            | Expression::Error { .. } => false,
        }
    }

    fn definition_at(&self, span: Span) -> Option<DefinitionRef> {
        self.definition_locations.get(&Self::span_key(span)).copied()
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
                let reason = if actual_kind.is_some() {
                    IncompleteReason::WrongKind(name.name.clone())
                } else {
                    IncompleteReason::MissingReference(name.name.clone())
                };
                self.incomplete(name.span, reason);
            }
            BusTarget::Ambiguous { .. } => {
                self.incomplete(name.span, IncompleteReason::AmbiguousReference(name.name.clone()));
            }
            BusTarget::Bus(_) | BusTarget::Opaque { .. } => {}
        }
        result
    }

    fn check_arity(&mut self, target: &CallTarget, arguments: usize, span: Span) -> bool {
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
                return false;
            }
        }
        true
    }

    fn check_template_arguments(&mut self, arguments: &[ExprId], span: Span) -> bool {
        let knownness =
            arguments.iter().fold(Knownness::Constant, |acc, id| acc.join(self.knownness(*id)));
        if knownness == Knownness::WitnessDependent {
            self.diagnostic(
                SemanticCode::NonComputableExpression,
                Severity::Error,
                span,
                "template arguments depend on witness values".into(),
            );
        }
        if !knownness.is_compile_time() {
            self.incomplete(span, IncompleteReason::NonCompileTime);
            return false;
        }
        true
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
        self.lower_block_into(&definition.body.statements, body, true);
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
        match statement {
            Statement::Block(_)
            | Statement::Declaration(_)
            | Statement::Assignment { .. }
            | Statement::PostfixUpdate { .. }
            | Statement::Constraint { .. } => self.lower_local_statement(statement),
            Statement::If { .. } | Statement::For { .. } | Statement::While { .. } => {
                self.lower_control_statement(statement)
            }
            Statement::Return { .. }
            | Statement::Assert { .. }
            | Statement::Log { .. }
            | Statement::AnonymousCall { .. }
            | Statement::Error { .. } => self.lower_terminal_statement(statement),
        }
    }

    fn lower_local_statement(&mut self, statement: &Statement) -> Vec<Effect> {
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
                if !Self::symbolic_indices(&path).all(|id| self.expression_is_checked(id)) {
                    return vec![self.opaque(span, IncompleteReason::UnknownType)];
                }
                let knownness = self.access_knownness(&path);
                self.hir.symbols[path.terminal.index].knownness = knownness;
                vec![Effect::Update { target: path, operator: *operator, span }]
            }
            Statement::Constraint { left, right, .. } => {
                if matches!(self.current_definition, Some(DefinitionRef::Function(_))) {
                    self.diagnostic(
                        SemanticCode::ConstraintInFunction,
                        Severity::Error,
                        span,
                        "a function cannot generate constraints".into(),
                    );
                    return vec![self.opaque(
                        span,
                        IncompleteReason::Unsupported("constraint in function".into()),
                    )];
                }
                let left = self.lower_expression(left);
                let right = self.lower_expression(right);
                if !self.expression_is_checked(left) || !self.expression_is_checked(right) {
                    return vec![self.opaque(span, IncompleteReason::UnknownType)];
                }
                vec![Effect::EqualityConstraint { left, right, span }]
            }
            _ => {
                let reason = IncompleteReason::Unsupported("local statement form".into());
                vec![self.opaque(span, reason)]
            }
        }
    }

    fn lower_control_statement(&mut self, statement: &Statement) -> Vec<Effect> {
        let span = statement.span();
        match statement {
            Statement::If { condition, then_branch, else_branch, .. } => {
                let condition = self.lower_expression(condition);
                let before = self.snapshot_knownness();
                let then_block = self.lower_branch(then_branch);
                let after_then = self.snapshot_knownness();
                self.restore_knownness(&before);
                let else_block = else_branch.as_ref().map(|branch| self.lower_branch(branch));
                self.join_knownness(&after_then, &before);
                if !self.knownness(condition).is_compile_time() {
                    return vec![self.opaque(span, IncompleteReason::NonCompileTime)];
                }
                vec![Effect::If { condition, then_block, else_block, span }]
            }
            Statement::For { initializer, condition, step, body, .. } => {
                self.scopes.enter();
                let initializer_block = self.hir.add_block(initializer.span());
                self.lower_block_into(std::slice::from_ref(initializer), initializer_block, false);
                let before_loop = self.snapshot_knownness();
                let condition = self.lower_expression(condition);
                let body = self.lower_branch(body);
                let after_body = self.snapshot_knownness();
                let step = self.lower_branch(step);
                let stable_condition = self.loop_condition_is_stable(condition, &before_loop);
                self.join_knownness(&before_loop, &after_body);
                self.scopes.leave();
                if !self.knownness(condition).is_compile_time() || !stable_condition {
                    return vec![self.opaque(span, IncompleteReason::NonCompileTime)];
                }
                vec![Effect::For { initializer: initializer_block, condition, step, body, span }]
            }
            Statement::While { condition, body, .. } => {
                let before = self.snapshot_knownness();
                let condition = self.lower_expression(condition);
                let body = self.lower_branch(body);
                let stable_condition = self.loop_condition_is_stable(condition, &before);
                self.join_knownness(&before, &before);
                if !self.knownness(condition).is_compile_time() || !stable_condition {
                    return vec![self.opaque(span, IncompleteReason::NonCompileTime)];
                }
                vec![Effect::While { condition, body, span }]
            }
            _ => {
                vec![self
                    .opaque(span, IncompleteReason::Unsupported("control statement form".into()))]
            }
        }
    }

    fn lower_terminal_statement(&mut self, statement: &Statement) -> Vec<Effect> {
        let span = statement.span();
        match statement {
            Statement::Return { value, .. } => {
                if !matches!(self.current_definition, Some(DefinitionRef::Function(_))) {
                    self.diagnostic(
                        SemanticCode::TemplateReturn,
                        Severity::Error,
                        span,
                        "return is only valid in a function".into(),
                    );
                    return vec![self.opaque(
                        span,
                        IncompleteReason::Unsupported("return outside function".into()),
                    )];
                }
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
            _ => {
                vec![self
                    .opaque(span, IncompleteReason::Unsupported("terminal statement form".into()))]
            }
        }
    }

    fn snapshot_knownness(&self) -> Vec<Knownness> {
        self.hir.symbols.iter().map(|symbol| symbol.knownness).collect()
    }

    fn symbolic_indices(path: &AccessPath) -> impl Iterator<Item = ExprId> + '_ {
        path.steps.iter().filter_map(|step| match step {
            AccessStep::Index { index: ArrayIndex::Symbolic(id), .. } => Some(*id),
            AccessStep::Index { index: ArrayIndex::Constant(_), .. }
            | AccessStep::Port { .. }
            | AccessStep::Tag { .. } => None,
        })
    }

    fn access_knownness(&self, path: &AccessPath) -> Knownness {
        let mut knownness = self.hir.symbols[path.terminal.index].knownness;
        for id in Self::symbolic_indices(path) {
            knownness = knownness.join(self.knownness(id));
        }
        knownness
    }

    fn expression_is_checked(&self, id: ExprId) -> bool {
        let Some(expression) = self.hir.expression(id) else { return false };
        match &expression.kind {
            ExprKind::Number(_) => true,
            ExprKind::Access(path) => {
                Self::symbolic_indices(path).all(|id| self.expression_is_checked(id))
            }
            ExprKind::Call { target, arguments } => {
                matches!(target, CallTarget::Function(_) | CallTarget::Template(_))
                    && arguments.iter().all(|id| self.expression_is_checked(*id))
            }
            ExprKind::AnonymousComponent { component, arguments, inputs } => {
                let target = self.hir.components[component.index].target.as_ref();
                expression.knownness != Knownness::Opaque
                    && matches!(target, Some(CallTarget::Template(_)))
                    && arguments.iter().all(|id| self.expression_is_checked(*id))
                    && inputs.iter().all(|input| {
                        matches!(input.target, AnonymousInputTarget::Port(_))
                            && self.expression_is_checked(input.value)
                    })
            }
            ExprKind::Array(values) | ExprKind::Tuple(values) => {
                values.iter().all(|id| self.expression_is_checked(*id))
            }
            ExprKind::Unary { operand, .. } | ExprKind::Parallel(operand) => {
                self.expression_is_checked(*operand)
            }
            ExprKind::Binary { left, right, .. } => {
                self.expression_is_checked(*left) && self.expression_is_checked(*right)
            }
            ExprKind::Ternary { condition, yes, no } => {
                self.expression_is_checked(*condition)
                    && self.expression_is_checked(*yes)
                    && self.expression_is_checked(*no)
            }
            ExprKind::Opaque(_) => false,
        }
    }

    fn loop_condition_is_stable(&self, condition: ExprId, before: &[Knownness]) -> bool {
        let mut pending = vec![condition];
        while let Some(id) = pending.pop() {
            let Some(expression) = self.hir.expression(id) else { return false };
            match &expression.kind {
                ExprKind::Access(path) => {
                    let Some(initial) = before.get(path.terminal.index) else { return false };
                    if self.hir.symbols[path.terminal.index].knownness != *initial {
                        return false;
                    }
                    pending.extend(Self::symbolic_indices(path));
                }
                ExprKind::Unary { operand, .. } | ExprKind::Parallel(operand) => {
                    pending.push(*operand);
                }
                ExprKind::Binary { left, right, .. } => pending.extend([*left, *right]),
                ExprKind::Ternary { condition, yes, no } => {
                    pending.extend([*condition, *yes, *no]);
                }
                ExprKind::Array(elements) | ExprKind::Tuple(elements) => {
                    pending.extend(elements.iter().copied());
                }
                ExprKind::Number(_) => {}
                ExprKind::Call { .. }
                | ExprKind::AnonymousComponent { .. }
                | ExprKind::Opaque(_) => return false,
            }
        }
        true
    }

    fn restore_knownness(&mut self, snapshot: &[Knownness]) {
        for (symbol, knownness) in self.hir.symbols.iter_mut().zip(snapshot) {
            symbol.knownness = *knownness;
        }
    }

    fn join_knownness(&mut self, first: &[Knownness], second: &[Knownness]) {
        for (index, (first, second)) in first.iter().zip(second).enumerate() {
            let current = self.hir.symbols[index].knownness;
            self.hir.symbols[index].knownness = current.join(*first).join(*second);
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

    fn declare(&mut self, name: &Identifier, kind: SymbolKind) -> Option<SymbolId> {
        if self.scopes.current(&name.name).is_some() {
            self.diagnostic(
                SemanticCode::DuplicateSymbol,
                Severity::Error,
                name.span,
                format!("duplicate local symbol `{}`", name.name),
            );
            return None;
        } else if let Some(outer) = self.scopes.outer(&name.name) {
            if kind == SymbolKind::Variable
                && matches!(
                    self.hir.symbols[outer.index].kind,
                    SymbolKind::Variable | SymbolKind::Parameter
                )
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
        self.scopes.insert(name.name.clone(), id);
        Some(id)
    }

    fn lower_declaration(&mut self, declaration: &Declaration) -> Vec<Effect> {
        if matches!(self.current_definition, Some(DefinitionRef::Function(_)))
            && !matches!(declaration.kind, DeclarationKind::Variable)
        {
            self.diagnostic(
                SemanticCode::ForbiddenDeclaration,
                Severity::Error,
                declaration.span,
                "function contains a template-only declaration".into(),
            );
            return vec![self.opaque(
                declaration.span,
                IncompleteReason::Unsupported("template element in function".into()),
            )];
        }
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
        let bus_arguments = self.lower_bus_arguments(declaration);
        let bus_type = self.lower_bus_type(declaration, &bus_arguments);
        let mut effects = Vec::new();
        for declared in &declaration.symbols {
            effects.extend(self.lower_declared_symbol(
                declared,
                kind,
                bus_type.clone(),
                &bus_arguments,
                tags,
            ));
        }
        effects.extend(self.lower_tuple_initialization(declaration));
        effects
    }

    fn lower_bus_arguments(&mut self, declaration: &Declaration) -> Vec<ExprId> {
        let DeclarationKind::Bus { arguments, .. } = &declaration.kind else { return Vec::new() };
        arguments
            .values()
            .iter()
            .map(|argument| {
                let id = self.lower_expression(argument);
                self.expect_compile_time(id, argument.span(), false);
                id
            })
            .collect()
    }

    fn lower_bus_type(
        &mut self,
        declaration: &Declaration,
        arguments: &[ExprId],
    ) -> Option<BusTarget> {
        let DeclarationKind::Bus { type_name, .. } = &declaration.kind else { return None };
        let predeclared = declaration.symbols.first().and_then(|declared| {
            self.predeclared_ports.get(&Self::span_key(declared.name.span)).copied()
        });
        let mut bus_type = if let Some(symbol) = predeclared {
            match self.hir.symbols[symbol.index].bus_type.clone() {
                Some(BusTarget::Opaque { reason: IncompleteReason::UnknownType }) => {
                    Some(self.resolve_bus(type_name))
                }
                other => other,
            }
        } else {
            Some(self.resolve_bus(type_name))
        };
        if let Some(BusTarget::Bus(id)) = bus_type {
            let expected = self.hir.buses[id.index].parameters.len();
            if expected != arguments.len() {
                self.diagnostic(
                    SemanticCode::WrongArity,
                    Severity::Error,
                    declaration.span,
                    format!("bus expects {expected} arguments, found {}", arguments.len()),
                );
                self.incomplete(
                    declaration.span,
                    IncompleteReason::Unsupported("wrong bus argument arity".into()),
                );
                bus_type = Some(BusTarget::Opaque {
                    reason: IncompleteReason::Unsupported("wrong bus argument arity".into()),
                });
            }
        }
        if !arguments.iter().all(|id| self.knownness(*id).is_compile_time()) {
            bus_type = Some(BusTarget::Opaque { reason: IncompleteReason::NonCompileTime });
        }
        bus_type
    }

    fn lower_declared_symbol(
        &mut self,
        declared: &DeclaredSymbol,
        kind: SymbolKind,
        bus_type: Option<BusTarget>,
        bus_arguments: &[ExprId],
        tags: &[Identifier],
    ) -> Vec<Effect> {
        let symbol = if let Some(symbol) =
            self.predeclared_ports.get(&Self::span_key(declared.name.span)).copied()
        {
            self.bind_predeclared(&declared.name, symbol).then_some(symbol)
        } else {
            self.declare(&declared.name, kind)
        };
        let Some(symbol) = symbol else {
            return vec![self.opaque(
                declared.span,
                IncompleteReason::AmbiguousReference(declared.name.name.clone()),
            )];
        };
        self.hir.symbols[symbol.index].bus_type = bus_type;
        self.hir.symbols[symbol.index].bus_arguments = bus_arguments.to_vec();
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
        let mut effects = vec![Effect::Declaration { symbol, span: declared.span }];
        if let Some((operator, value)) = &declared.initialization {
            effects.push(self.assignment_for_symbol(symbol, *operator, value, declared.span));
        }
        effects
    }

    fn lower_tuple_initialization(&mut self, declaration: &Declaration) -> Vec<Effect> {
        let Some((operator, value)) = &declaration.tuple_initialization else { return Vec::new() };
        let mut effects = Vec::new();
        if let Expression::Tuple { elements, .. } = value {
            if elements.len() == declaration.symbols.len() {
                for (declared, element) in declaration.symbols.iter().zip(elements) {
                    if let Some(symbol) = self.scopes.resolve(&declared.name.name) {
                        if self.hir.symbols[symbol.index].span != declared.name.span {
                            effects.push(self.opaque(
                                declared.span,
                                IncompleteReason::AmbiguousReference(declared.name.name.clone()),
                            ));
                            continue;
                        }
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
        effects
    }

    fn bind_predeclared(&mut self, name: &Identifier, symbol: SymbolId) -> bool {
        if self.scopes.current(&name.name).is_some() {
            self.diagnostic(
                SemanticCode::DuplicateSymbol,
                Severity::Error,
                name.span,
                format!("duplicate local symbol `{}`", name.name),
            );
            false
        } else {
            self.scopes.insert(name.name.clone(), symbol);
            true
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
        if !self.expression_is_checked(value)
            || !Self::symbolic_indices(&path).all(|id| self.expression_is_checked(id))
        {
            return self.opaque(span, IncompleteReason::UnknownType);
        }
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
                        if operator == AssignmentOperator::Assign && path.steps.is_empty() {
                            next
                        } else {
                            current.join(next).join(self.access_knownness(&path))
                        };
                }
                if kind == SymbolKind::Component
                    && self.expression_type(value) == ValueType::Unknown
                {
                    return self.opaque(span, IncompleteReason::InvalidAssignment);
                }
                if kind == SymbolKind::Component {
                    Effect::ComponentInstantiation { target: path, value, span }
                } else {
                    Effect::VariableAssignment { target: path, value, span }
                }
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
            Expression::Call { name, arguments, span } => {
                Some((name, arguments.as_slice(), *span, false))
            }
            Expression::Parallel { operand, .. } => match operand.as_ref() {
                Expression::Call { name, arguments, span } => {
                    Some((name, arguments.as_slice(), *span, true))
                }
                _ => None,
            },
            _ => None,
        };
        let Some((name, arguments, span, parallel)) = call else {
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
        let mut target = self.resolve_call(name, DefinitionKind::Template);
        let valid_arity = self.check_arity(&target, arguments.len(), span);
        let valid_arguments = self.check_template_arguments(&arguments, span);
        if !valid_arity {
            target = CallTarget::Opaque {
                reason: IncompleteReason::Unsupported("wrong argument arity".into()),
            };
        } else if !valid_arguments {
            target = CallTarget::Opaque { reason: IncompleteReason::NonCompileTime };
        }
        if let Some(component) = self.components.get(&symbol) {
            self.hir.components[component.index].target = Some(target.clone());
        }
        let ty = match target {
            CallTarget::Template(id) => ValueType::Component(id),
            _ => ValueType::Unknown,
        };
        let call =
            self.add_expression(ExprKind::Call { target, arguments }, Knownness::Opaque, span, ty);
        if parallel {
            self.add_expression(ExprKind::Parallel(call), Knownness::Opaque, value.span(), ty)
        } else {
            call
        }
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
        let mut state = AccessState {
            ty: self.symbol_type(root),
            terminal: root,
            remaining_dimensions: self.hir.symbols[root.index].rank,
            component_input: false,
            component_output: false,
            indexed_current: false,
            steps: Vec::new(),
        };
        for part in access {
            let valid = match part {
                Access::Index { expression, span } => {
                    self.apply_access_index(&mut state, expression, *span)
                }
                Access::Field { field, span } => self.apply_access_field(&mut state, field, *span),
            };
            if !valid {
                return None;
            }
        }
        Some(AccessPath {
            root,
            steps: state.steps,
            terminal: state.terminal,
            component_input: state.component_input,
            component_output: state.component_output,
            span: *span,
        })
    }

    fn apply_access_index(
        &mut self,
        state: &mut AccessState,
        expression: &Expression,
        span: Span,
    ) -> bool {
        if state.remaining_dimensions == 0 {
            self.diagnostic(
                SemanticCode::InvalidArrayAccess,
                Severity::Error,
                span,
                "index applied to a scalar or beyond declared array rank".into(),
            );
            self.incomplete(span, IncompleteReason::InvalidAssignment);
            return false;
        }
        let id = self.lower_expression(expression);
        let index = match &self.hir.expressions[id.index].kind {
            ExprKind::Number(value) => ArrayIndex::Constant(value.clone()),
            _ => ArrayIndex::Symbolic(id),
        };
        state.steps.push(AccessStep::Index { index, span });
        state.remaining_dimensions -= 1;
        state.indexed_current = true;
        true
    }

    fn apply_access_field(
        &mut self,
        state: &mut AccessState,
        field: &Identifier,
        span: Span,
    ) -> bool {
        let is_tag = self.hir.symbols[state.terminal.index]
            .tags
            .iter()
            .any(|tag| self.hir.symbols[tag.index].name == field.name);
        if is_tag {
            if let ValueType::Bus(id) = state.ty {
                let collides = self.hir.buses[id.index].ports.iter().any(|port| {
                    let symbol = self.hir.ports[port.index].symbol;
                    self.hir.symbols[symbol.index].name == field.name
                });
                if collides {
                    self.incomplete(span, IncompleteReason::AmbiguousReference(field.name.clone()));
                    return false;
                }
            }
        }
        if is_tag && state.indexed_current {
            self.diagnostic(
                SemanticCode::InvalidTagAfterArray,
                Severity::Error,
                span,
                "tag access after array indexing is invalid".into(),
            );
            self.incomplete(span, IncompleteReason::InvalidAssignment);
            return false;
        }
        if state.remaining_dimensions != 0 && !is_tag {
            self.diagnostic(
                SemanticCode::InvalidArrayAccess,
                Severity::Error,
                span,
                "field access requires a fully indexed array".into(),
            );
            self.incomplete(span, IncompleteReason::InvalidAssignment);
            return false;
        }
        let from_component = matches!(state.ty, ValueType::Component(_));
        let Some((step, symbol, next)) =
            self.resolve_field(state.ty, state.terminal, field, state.component_input)
        else {
            return false;
        };
        if from_component {
            if let AccessStep::Port { port, .. } = &step {
                state.component_input |=
                    self.hir.ports[port.index].direction == Some(PortDirection::Input);
                state.component_output |=
                    self.hir.ports[port.index].direction == Some(PortDirection::Output);
            }
        }
        state.steps.push(match step {
            AccessStep::Port { port, .. } => AccessStep::Port { port, span },
            AccessStep::Tag { symbol, .. } => AccessStep::Tag { symbol, span },
            AccessStep::Index { .. } => return false,
        });
        state.terminal = symbol;
        state.ty = next;
        state.remaining_dimensions = self.hir.symbols[symbol.index].rank;
        state.indexed_current = false;
        true
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
        external_input: bool,
    ) -> Option<(AccessStep, SymbolId, ValueType)> {
        let tag = self.hir.symbols[current.index]
            .tags
            .iter()
            .find(|tag| self.hir.symbols[tag.index].name == field.name)
            .copied();
        if let Some(symbol) = tag {
            if external_input {
                self.diagnostic(
                    SemanticCode::InputTagAccess,
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
            let matching: Vec<_> = ports
                .iter()
                .filter(|port| {
                    self.hir.symbols[self.hir.ports[port.index].symbol.index].name == field.name
                })
                .copied()
                .collect();
            if matching.len() > 1 {
                self.incomplete(
                    field.span,
                    IncompleteReason::AmbiguousReference(field.name.clone()),
                );
                return None;
            }
            if let Some(port) = matching.first().copied() {
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
            let code = if self.hir.symbols[current.index].kind == SymbolKind::Signal {
                SemanticCode::InvalidTag
            } else {
                SemanticCode::InvalidSignalAccess
            };
            self.diagnostic(
                code,
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
            Expression::Name { .. } => self.lower_named_expression(expression),
            Expression::Call { name, arguments, .. } => {
                self.lower_function_call(name, arguments, span)
            }
            Expression::AnonymousCall(call) => self.lower_anonymous(call),
            Expression::Array { elements, .. } => self.lower_collection(elements, span, true),
            Expression::Tuple { elements, .. } => self.lower_collection(elements, span, false),
            Expression::Unary { .. }
            | Expression::Binary { .. }
            | Expression::Ternary { .. }
            | Expression::Parallel { .. } => self.lower_operation(expression),
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

    fn lower_named_expression(&mut self, expression: &Expression) -> ExprId {
        let span = expression.span();
        let Some(path) = self.lower_access(expression) else {
            return self.add_expression(
                ExprKind::Opaque(IncompleteReason::UnknownType),
                Knownness::Opaque,
                span,
                ValueType::Unknown,
            );
        };
        let ty = self.access_type(&path);
        if ty == ValueType::Unknown
            && self.hir.symbols[path.terminal.index].kind != SymbolKind::Parameter
        {
            self.incomplete(span, IncompleteReason::UnknownType);
            return self.add_expression(
                ExprKind::Opaque(IncompleteReason::UnknownType),
                Knownness::Opaque,
                span,
                ValueType::Unknown,
            );
        }
        let knownness = self.access_knownness(&path);
        if knownness == Knownness::Opaque {
            self.incomplete(span, IncompleteReason::UnknownType);
        }
        self.add_expression(ExprKind::Access(path), knownness, span, ty)
    }

    fn lower_function_call(
        &mut self,
        name: &Identifier,
        values: &[Expression],
        span: Span,
    ) -> ExprId {
        let arguments: Vec<_> = values.iter().map(|value| self.lower_expression(value)).collect();
        let mut target = self.resolve_call(name, DefinitionKind::Function);
        if !self.check_arity(&target, arguments.len(), span) {
            target = CallTarget::Opaque {
                reason: IncompleteReason::Unsupported("wrong argument arity".into()),
            };
        }
        let ty = if matches!(target, CallTarget::Function(_)) {
            ValueType::Plain
        } else {
            ValueType::Unknown
        };
        self.add_expression(ExprKind::Call { target, arguments }, Knownness::Opaque, span, ty)
    }

    fn lower_collection(&mut self, values: &[Expression], span: Span, array: bool) -> ExprId {
        let elements: Vec<_> = values.iter().map(|value| self.lower_expression(value)).collect();
        let knownness =
            elements.iter().fold(Knownness::Constant, |acc, id| acc.join(self.knownness(*id)));
        let ty = if elements.iter().all(|id| self.expression_is_checked(*id)) {
            self.array_type(&elements)
        } else {
            ValueType::Unknown
        };
        if array {
            self.array_types.insert(Self::span_key(span), ty);
            self.add_expression(ExprKind::Array(elements), knownness, span, ty)
        } else {
            self.add_expression(ExprKind::Tuple(elements), knownness, span, ty)
        }
    }

    fn lower_operation(&mut self, expression: &Expression) -> ExprId {
        let span = expression.span();
        match expression {
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
                self.add_expression(
                    ExprKind::Binary { operator: *operator, left, right },
                    self.knownness(left).join(self.knownness(right)),
                    span,
                    ValueType::Plain,
                )
            }
            Expression::Ternary { condition, yes, no, .. } => {
                let condition = self.lower_expression(condition);
                let yes = self.lower_expression(yes);
                let no = self.lower_expression(no);
                let ty = if self.expression_type(yes) == self.expression_type(no) {
                    self.expression_type(yes)
                } else {
                    ValueType::Unknown
                };
                let knownness =
                    self.knownness(condition).join(self.knownness(yes)).join(self.knownness(no));
                self.add_expression(ExprKind::Ternary { condition, yes, no }, knownness, span, ty)
            }
            Expression::Parallel { .. } => {
                self.incomplete(span, IncompleteReason::Unsupported("parallel value".into()));
                self.add_expression(
                    ExprKind::Opaque(IncompleteReason::Unsupported("parallel value".into())),
                    Knownness::Opaque,
                    span,
                    ValueType::Unknown,
                )
            }
            _ => self.add_expression(
                ExprKind::Opaque(IncompleteReason::Unsupported("expression operation".into())),
                Knownness::Opaque,
                span,
                ValueType::Unknown,
            ),
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
        let mut target = self.resolve_call(&call.name, DefinitionKind::Template);
        let arguments: Vec<_> =
            call.parameters.iter().map(|value| self.lower_expression(value)).collect();
        let valid_arity = self.check_arity(&target, arguments.len(), call.span);
        let valid_arguments = self.check_template_arguments(&arguments, call.span);
        if !valid_arity {
            target = CallTarget::Opaque {
                reason: IncompleteReason::Unsupported("wrong argument arity".into()),
            };
        } else if !valid_arguments {
            target = CallTarget::Opaque { reason: IncompleteReason::NonCompileTime };
        }
        let template = if let CallTarget::Template(id) = target { Some(id) } else { None };
        let mut inputs: Vec<_> = call
            .inputs
            .iter()
            .enumerate()
            .map(|(position, input)| self.lower_anonymous_input(template, input, position))
            .collect();
        let valid_inputs = template.is_some_and(|template| {
            self.validate_anonymous_inputs(template, &mut inputs, call.span)
        });
        let symbol = self.hir.add_symbol(
            format!("<anonymous:{}>", call.span.start()),
            SymbolKind::Component,
            call.span,
        );
        let component = self.hir.add_component(symbol, call.span);
        let valid_target = matches!(target, CallTarget::Template(_));
        self.hir.components[component.index].target = Some(target);
        self.add_expression(
            ExprKind::AnonymousComponent { component, arguments, inputs },
            if valid_target && valid_inputs {
                Knownness::WitnessDependent
            } else {
                Knownness::Opaque
            },
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
        let Some(template) = template else {
            return AnonymousInputEffect {
                target: AnonymousInputTarget::Opaque(IncompleteReason::UnknownType),
                operator,
                value,
                span,
            };
        };
        let ports: Vec<_> = {
            let inputs = self.hir.templates[template.index]
                .ports
                .iter()
                .filter(|port| self.hir.ports[port.index].direction == Some(PortDirection::Input));
            if let Some(name) = name {
                inputs
                    .into_iter()
                    .filter(|port| {
                        self.hir.symbols[self.hir.ports[port.index].symbol.index].name == name.name
                    })
                    .copied()
                    .collect()
            } else {
                inputs.into_iter().nth(position).copied().into_iter().collect()
            }
        };
        if ports.len() > 1 {
            let reason = IncompleteReason::AmbiguousReference(
                name.map_or_else(|| position.to_string(), |name| name.name.clone()),
            );
            self.incomplete(span, reason.clone());
            return AnonymousInputEffect {
                target: AnonymousInputTarget::Opaque(reason),
                operator,
                value,
                span,
            };
        }
        let port = ports.first().copied();
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

    fn validate_anonymous_inputs(
        &mut self,
        template: TemplateId,
        inputs: &mut [AnonymousInputEffect],
        span: Span,
    ) -> bool {
        let mut names = BTreeSet::new();
        for port in &self.hir.templates[template.index].ports {
            if self.hir.ports[port.index].direction != Some(PortDirection::Input) {
                continue;
            }
            let symbol = self.hir.ports[port.index].symbol;
            if !names.insert(self.hir.symbols[symbol.index].name.as_str()) {
                self.incomplete(
                    span,
                    IncompleteReason::AmbiguousReference(
                        self.hir.symbols[symbol.index].name.clone(),
                    ),
                );
                return false;
            }
        }
        let mut used = BTreeSet::new();
        for input in inputs.iter_mut() {
            let AnonymousInputTarget::Port(port) = input.target else { continue };
            if !used.insert(port) {
                self.diagnostic(
                    SemanticCode::AnonymousInput,
                    Severity::Error,
                    input.span,
                    "anonymous input is assigned more than once".into(),
                );
                self.incomplete(input.span, IncompleteReason::InvalidAssignment);
                input.target = AnonymousInputTarget::Opaque(IncompleteReason::InvalidAssignment);
            }
        }
        if inputs.iter().any(|input| matches!(input.target, AnonymousInputTarget::Opaque(_))) {
            return false;
        }
        let missing = self.hir.templates[template.index].ports.iter().any(|port| {
            self.hir.ports[port.index].direction == Some(PortDirection::Input)
                && !used.contains(port)
        });
        if missing {
            self.diagnostic(
                SemanticCode::AnonymousInput,
                Severity::Error,
                span,
                "anonymous call does not assign every input port".into(),
            );
            self.incomplete(span, IncompleteReason::InvalidAssignment);
        }
        !missing
    }

    fn lower_mains(&mut self) {
        for file in &self.source.files {
            for item in &file.outcome.ast.items {
                let Item::Main { instance, span, .. } = item else { continue };
                let call = match instance {
                    Expression::Call { name, arguments, .. } => {
                        Some((name, arguments.as_slice(), false))
                    }
                    Expression::Parallel { operand, .. } => match operand.as_ref() {
                        Expression::Call { name, arguments, .. } => {
                            Some((name, arguments.as_slice(), true))
                        }
                        _ => None,
                    },
                    _ => None,
                };
                if let Some((name, arguments, parallel)) = call {
                    self.scopes.enter();
                    let arguments: Vec<_> =
                        arguments.iter().map(|value| self.lower_expression(value)).collect();
                    self.scopes.leave();
                    let mut target = self.resolve_call(name, DefinitionKind::Template);
                    let valid_arity = self.check_arity(&target, arguments.len(), *span);
                    let valid_arguments = self.check_template_arguments(&arguments, *span);
                    if !valid_arity {
                        target = CallTarget::Opaque {
                            reason: IncompleteReason::Unsupported("wrong argument arity".into()),
                        };
                    } else if !valid_arguments {
                        target = CallTarget::Opaque { reason: IncompleteReason::NonCompileTime };
                    }
                    self.hir.mains.push(Main { target, arguments, parallel, span: *span });
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
            let reason = match diagnostic.kind {
                DiagnosticKind::MissingInclude
                | DiagnosticKind::FileRead
                | DiagnosticKind::CyclicInclude => IncompleteReason::Include,
                _ => IncompleteReason::Syntax,
            };
            self.incomplete.push(IncompleteRegion {
                location: IncompleteLocation::from(&diagnostic.location),
                reason,
            });
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
        definition_locations: BTreeMap::new(),
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
    lowerer.incomplete.sort_by(|left, right| match (&left.location, &right.location) {
        (IncompleteLocation::Source(left), IncompleteLocation::Source(right)) => (
            left.source().index(),
            left.start(),
            left.end(),
        )
            .cmp(&(right.source().index(), right.start(), right.end())),
        (IncompleteLocation::Source(_), IncompleteLocation::Path(_)) => std::cmp::Ordering::Less,
        (IncompleteLocation::Path(_), IncompleteLocation::Source(_)) => std::cmp::Ordering::Greater,
        (IncompleteLocation::Path(left), IncompleteLocation::Path(right)) => left.cmp(right),
    });
    LoweredProject {
        hir: lowerer.hir,
        diagnostics: lowerer.diagnostics,
        syntax_diagnostics: source.diagnostics.clone(),
        incomplete: lowerer.incomplete,
    }
}
