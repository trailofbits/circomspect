use crate::hir::lower::*;

impl Lowerer<'_> {
    pub(super) fn lower_access(&mut self, expression: &Expression) -> Option<AccessPath> {
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
        if !self.hir.symbols[root.index].shape_checked {
            self.incomplete(*span, IncompleteReason::UnknownType);
            return None;
        }
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

    pub(super) fn apply_access_index(
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

    pub(super) fn apply_access_field(
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

    pub(super) fn symbol_type(&self, symbol: SymbolId) -> ValueType {
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

    pub(super) fn resolve_field(
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
                if !self.hir.symbols[symbol.index].shape_checked {
                    self.incomplete(field.span, IncompleteReason::UnknownType);
                    return None;
                }
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

    pub(super) fn lower_expression(&mut self, expression: &Expression) -> ExprId {
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

    pub(super) fn lower_named_expression(&mut self, expression: &Expression) -> ExprId {
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

    pub(super) fn lower_function_call(
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

    pub(super) fn lower_collection(
        &mut self,
        values: &[Expression],
        span: Span,
        array: bool,
    ) -> ExprId {
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

    pub(super) fn lower_operation(&mut self, expression: &Expression) -> ExprId {
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

    pub(super) fn access_type(&self, path: &AccessPath) -> ValueType {
        self.symbol_type(path.terminal)
    }

    pub(super) fn array_type(&self, elements: &[ExprId]) -> ValueType {
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

    pub(super) fn span_key(span: Span) -> (usize, usize, usize) {
        (span.source().index(), span.start(), span.end())
    }

    pub(super) fn lower_anonymous(&mut self, call: &AnonymousCallExpr) -> ExprId {
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

    pub(super) fn lower_anonymous_input(
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

    pub(super) fn validate_anonymous_inputs(
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

    pub(super) fn lower_mains(&mut self) {
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
}
