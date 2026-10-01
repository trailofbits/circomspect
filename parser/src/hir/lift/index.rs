use crate::hir::lift::*;

struct PortContext<'a> {
    reference: DefinitionRef,
    kind: SymbolKind,
    direction: Option<PortDirection>,
    tags: &'a [Identifier],
    bus_type: Option<BusTarget>,
    known_parameters: &'a BTreeSet<String>,
}

impl Lifter<'_> {
    pub(super) fn index_definitions(&mut self) {
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

    pub(super) fn report_duplicate_definitions(&mut self) {
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

    pub(super) fn definition_kind(reference: DefinitionRef) -> DefinitionKind {
        match reference {
            DefinitionRef::Function(_) => DefinitionKind::Function,
            DefinitionRef::Template(_) => DefinitionKind::Template,
            DefinitionRef::Bus(_) => DefinitionKind::Bus,
        }
    }

    pub(super) fn definition_span(&self, reference: DefinitionRef) -> Span {
        match reference {
            DefinitionRef::Function(id) => self.hir.functions[id.index].name_span,
            DefinitionRef::Template(id) => self.hir.templates[id.index].name_span,
            DefinitionRef::Bus(id) => self.hir.buses[id.index].name_span,
        }
    }

    pub(super) fn parameters(&mut self, definition: &Definition) -> Vec<SymbolId> {
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

    pub(super) fn index_parameters(&mut self) {
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

    pub(super) fn index_ports(&mut self) {
        for file in &self.source.files {
            for item in &file.outcome.ast.items {
                let Item::Definition(definition) = item else { continue };
                let Some(reference) = self.definition_at(definition.span) else { continue };
                self.index_definition_ports(definition, reference);
            }
        }
    }

    fn index_definition_ports(&mut self, definition: &Definition, reference: DefinitionRef) {
        let mut known_parameters = self.indexed_parameter_names(reference);
        for statement in &definition.body.statements {
            let Statement::Declaration(declaration) = statement else {
                known_parameters.clear();
                continue;
            };
            self.index_port_declaration(declaration, reference, &known_parameters);
            Self::remove_shadowed_parameters(&mut known_parameters, declaration);
        }
    }

    fn indexed_parameter_names(&self, reference: DefinitionRef) -> BTreeSet<String> {
        let parameters = match reference {
            DefinitionRef::Function(id) => &self.hir.functions[id.index].parameters,
            DefinitionRef::Template(id) => &self.hir.templates[id.index].parameters,
            DefinitionRef::Bus(id) => &self.hir.buses[id.index].parameters,
        };
        parameters.iter().map(|id| self.hir.symbols[id.index].name.clone()).collect()
    }

    fn index_port_declaration(
        &mut self,
        declaration: &Declaration,
        reference: DefinitionRef,
        known_parameters: &BTreeSet<String>,
    ) {
        let (kind, direction, tags) = match &declaration.kind {
            DeclarationKind::Signal { direction, tags } => {
                (SymbolKind::Signal, Self::direction(*direction), tags.as_slice())
            }
            DeclarationKind::Bus { direction, tags, .. } => {
                (SymbolKind::Bus, Self::direction(*direction), tags.as_slice())
            }
            DeclarationKind::Variable | DeclarationKind::Component => return,
        };
        if !Self::public_port(reference, direction) {
            return;
        }
        let bus_type = match &declaration.kind {
            DeclarationKind::Bus { type_name, arguments, .. } => Some(self.preindex_bus_type(
                type_name,
                arguments.values(),
                known_parameters,
                declaration.span,
            )),
            DeclarationKind::Signal { .. }
            | DeclarationKind::Variable
            | DeclarationKind::Component => None,
        };
        let context = PortContext { reference, kind, direction, tags, bus_type, known_parameters };
        for declared in &declaration.symbols {
            self.index_one_port(declared, &context);
        }
    }

    fn public_port(reference: DefinitionRef, direction: Option<PortDirection>) -> bool {
        match reference {
            DefinitionRef::Bus(_) => true,
            DefinitionRef::Template(_) => direction.is_some(),
            DefinitionRef::Function(_) => false,
        }
    }

    fn index_one_port(&mut self, declared: &DeclaredSymbol, context: &PortContext<'_>) {
        let symbol =
            self.hir.add_symbol(declared.name.name.clone(), context.kind, declared.name.span);
        let checked_shape = declared
            .dimensions
            .iter()
            .all(|value| Self::syntactic_compile_time(value, context.known_parameters));
        self.hir.symbols[symbol.index].bus_type = context.bus_type.clone();
        self.hir.symbols[symbol.index].rank = declared.dimensions.len();
        self.hir.symbols[symbol.index].shape_checked = checked_shape;
        let schema = Self::port_schema(context.kind, checked_shape, &context.bus_type);
        let port = self.hir.add_port(symbol, context.direction, schema, declared.span);
        for tag in context.tags {
            let tag_id = self.hir.add_symbol(tag.name.clone(), SymbolKind::Tag, tag.span);
            self.hir.symbols[symbol.index].tags.push(tag_id);
            self.hir.ports[port.index].tags.push(tag_id);
        }
        self.predeclared_ports.insert(Self::span_key(declared.name.span), symbol);
        match context.reference {
            DefinitionRef::Template(id) => self.hir.templates[id.index].ports.push(port),
            DefinitionRef::Bus(id) => self.hir.buses[id.index].ports.push(port),
            DefinitionRef::Function(_) => {}
        }
    }

    fn port_schema(
        kind: SymbolKind,
        checked_shape: bool,
        bus_type: &Option<BusTarget>,
    ) -> PortSchema {
        if !checked_shape {
            return PortSchema::Opaque(IncompleteReason::UnknownType);
        }
        match (kind, bus_type) {
            (SymbolKind::Signal, _) => PortSchema::Signal,
            (SymbolKind::Bus, Some(BusTarget::Bus(id))) => PortSchema::Bus(*id),
            _ => PortSchema::Opaque(IncompleteReason::UnknownType),
        }
    }

    pub(super) fn remove_shadowed_parameters(
        names: &mut BTreeSet<String>,
        declaration: &Declaration,
    ) {
        for symbol in &declaration.symbols {
            names.remove(&symbol.name.name);
        }
    }

    pub(super) fn preindex_bus_type(
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

    pub(super) fn syntactic_compile_time(
        expression: &Expression,
        parameters: &BTreeSet<String>,
    ) -> bool {
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

    pub(super) fn definition_at(&self, span: Span) -> Option<DefinitionRef> {
        self.definition_locations.get(&Self::span_key(span)).copied()
    }

    pub(super) fn resolve_call(
        &mut self,
        name: &Identifier,
        expected: DefinitionKind,
    ) -> CallTarget {
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

    pub(super) fn resolve_bus(&mut self, name: &Identifier) -> BusTarget {
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

    pub(super) fn check_arity(
        &mut self,
        target: &CallTarget,
        arguments: usize,
        span: Span,
    ) -> bool {
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

    pub(super) fn check_template_arguments(&mut self, arguments: &[ExprId], span: Span) -> bool {
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

    pub(super) fn lift_definitions(&mut self) {
        for kind in [DefinitionKind::Bus, DefinitionKind::Template, DefinitionKind::Function] {
            for file in &self.source.files {
                for item in &file.outcome.ast.items {
                    let Item::Definition(definition) = item else { continue };
                    let Some(reference) = self.definition_at(definition.span) else { continue };
                    if Self::definition_kind(reference) == kind {
                        self.lift_definition(definition, reference);
                    }
                }
            }
        }
    }

    pub(super) fn lift_definition(&mut self, definition: &Definition, reference: DefinitionRef) {
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
        self.lift_block_into(&definition.body.statements, body, true);
        self.scopes.leave();
        self.current_definition = None;
    }

    pub(super) fn lift_block_into(
        &mut self,
        statements: &[Statement],
        block: BlockId,
        scoped: bool,
    ) {
        if scoped {
            self.scopes.enter();
        }
        for statement in statements {
            let mut effects = self.lift_statement(statement);
            self.hir.blocks[block.index].effects.append(&mut effects);
        }
        if scoped {
            self.scopes.leave();
        }
    }

    pub(super) fn lift_branch(&mut self, statement: &Statement) -> BlockId {
        let block = self.hir.add_block(statement.span());
        match statement {
            Statement::Block(body) => self.lift_block_into(&body.statements, block, true),
            _ => self.lift_block_into(std::slice::from_ref(statement), block, true),
        }
        block
    }
}
