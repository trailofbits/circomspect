use crate::hir::lift::*;

impl Lifter<'_> {
    pub(super) fn lift_access(&mut self, expression: &Expression) -> Option<AccessPath> {
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
        if self.invalid_symbols.contains(&root) {
            self.incomplete(*span, IncompleteReason::InvalidAssignment);
            return None;
        }
        if !self.hir.symbols[root.index].shape_checked {
            self.incomplete(*span, IncompleteReason::UnknownType);
            return None;
        }
        let mut state = AccessState {
            ty: self.symbol_type(root),
            terminal: root,
            remaining_dimensions: self.symbol_rank(root),
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
        if state.remaining_dimensions == Some(0) {
            self.diagnostic(
                SemanticCode::InvalidArrayAccess,
                Severity::Error,
                span,
                "index applied to a scalar or beyond declared array rank".into(),
            );
            self.incomplete(span, IncompleteReason::InvalidAssignment);
            return false;
        }
        let id = self.lift_expression(expression);
        if !self.valid_index_expression(id, expression.span()) {
            return false;
        }
        let index = match &self.hir.expressions[id.index].kind {
            ExprKind::Number(value) => ArrayIndex::Constant(value.clone()),
            _ => ArrayIndex::Symbolic(id),
        };
        state.steps.push(AccessStep::Index { index, span });
        state.remaining_dimensions =
            state.remaining_dimensions.and_then(|rank| rank.checked_sub(1));
        state.indexed_current = true;
        true
    }

    fn valid_index_expression(&mut self, id: ExprId, span: Span) -> bool {
        if !self.expression_is_checked(id) {
            self.incomplete(span, IncompleteReason::UnknownType);
            return false;
        }
        match (self.expression_type(id), self.expression_rank(id)) {
            (ValueType::Plain, Some(0)) => true,
            (ValueType::Bus(_), _) => {
                self.diagnostic(
                    SemanticCode::InvalidArrayIndexBus,
                    Severity::Error,
                    span,
                    "array index must be a single arithmetic expression, found bus".into(),
                );
                self.incomplete(span, IncompleteReason::InvalidAssignment);
                false
            }
            (ValueType::Plain | ValueType::Component(_), Some(_)) => {
                self.diagnostic(
                    SemanticCode::InvalidArrayIndexDimension,
                    Severity::Error,
                    span,
                    "array index must be a single arithmetic expression".into(),
                );
                self.incomplete(span, IncompleteReason::InvalidAssignment);
                false
            }
            (ValueType::Plain | ValueType::Component(_) | ValueType::Unknown, None)
            | (ValueType::Unknown, Some(_)) => {
                self.incomplete(span, IncompleteReason::UnknownType);
                false
            }
        }
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
        if state.remaining_dimensions.is_some_and(|rank| rank != 0) && !is_tag {
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
        state.remaining_dimensions = self.symbol_rank(symbol);
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
                let next = match &self.hir.ports[port.index].schema {
                    PortSchema::Signal => ValueType::Plain,
                    PortSchema::Bus(id) => ValueType::Bus(*id),
                    PortSchema::Opaque(reason) => {
                        self.incomplete(field.span, reason.clone());
                        return None;
                    }
                };
                return Some((AccessStep::Port { port, span: field.span }, symbol, next));
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

    pub(super) fn lift_expression(&mut self, expression: &Expression) -> ExprId {
        let span = expression.span();
        match expression {
            Expression::Number { text, .. } => self.add_expression(
                ExprKind::Number(text.clone()),
                Knownness::Constant,
                span,
                ValueType::Plain,
            ),
            Expression::Name { .. } => self.lift_named_expression(expression),
            Expression::Call { name, arguments, .. } => {
                self.lift_function_call(name, arguments, span)
            }
            Expression::AnonymousCall(call) => self.lift_anonymous(call),
            Expression::Array { elements, .. } => self.lift_collection(elements, span, true),
            Expression::Tuple { elements, .. } => self.lift_collection(elements, span, false),
            Expression::Unary { .. }
            | Expression::Binary { .. }
            | Expression::Ternary { .. }
            | Expression::Parallel { .. } => self.lift_operation(expression),
            Expression::Group { expression, .. } => self.lift_expression(expression),
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

    pub(super) fn lift_named_expression(&mut self, expression: &Expression) -> ExprId {
        let span = expression.span();
        let Some(path) = self.lift_access(expression) else {
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

    pub(super) fn lift_function_call(
        &mut self,
        name: &Identifier,
        values: &[Expression],
        span: Span,
    ) -> ExprId {
        let arguments: Vec<_> = values.iter().map(|value| self.lift_expression(value)).collect();
        let mut target = self.resolve_call(name, DefinitionKind::Function);
        if !self.check_arity(&target, arguments.len(), span) {
            target = CallTarget::Opaque {
                reason: IncompleteReason::Unsupported("wrong argument arity".into()),
            };
        }
        for argument in &arguments {
            if matches!(
                self.expression_type(*argument),
                ValueType::Bus(_) | ValueType::Component(_)
            ) {
                let argument_span = self.hir.expressions[argument.index].span;
                self.diagnostic(
                    SemanticCode::InvalidCallArgument,
                    Severity::Error,
                    argument_span,
                    "function argument cannot be a bus or component".into(),
                );
                self.incomplete(argument_span, IncompleteReason::InvalidAssignment);
                target = CallTarget::Opaque { reason: IncompleteReason::InvalidAssignment };
            }
        }
        self.add_expression(
            ExprKind::Call { target, arguments },
            Knownness::Opaque,
            span,
            ValueType::Unknown,
        )
    }

    pub(super) fn lift_collection(
        &mut self,
        values: &[Expression],
        span: Span,
        array: bool,
    ) -> ExprId {
        let elements: Vec<_> = values.iter().map(|value| self.lift_expression(value)).collect();
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

    pub(super) fn lift_operation(&mut self, expression: &Expression) -> ExprId {
        let span = expression.span();
        match expression {
            Expression::Unary { operator, operand, .. } => {
                let operand = self.lift_expression(operand);
                let shape = self.scalar_shape(operand);
                if shape == ScalarShape::Invalid {
                    return self.opaque_expression(span);
                }
                let ty = if shape == ScalarShape::Deferred {
                    ValueType::Unknown
                } else {
                    ValueType::Plain
                };
                self.add_expression(
                    ExprKind::Unary { operator: *operator, operand },
                    self.knownness(operand),
                    span,
                    ty,
                )
            }
            Expression::Binary { operator, left, right, .. } => {
                let left = self.lift_expression(left);
                let right = self.lift_expression(right);
                let shape = self.scalar_shape(left).join(self.scalar_shape(right));
                if shape == ScalarShape::Invalid {
                    return self.opaque_expression(span);
                }
                let ty = if shape == ScalarShape::Deferred {
                    ValueType::Unknown
                } else {
                    ValueType::Plain
                };
                self.add_expression(
                    ExprKind::Binary { operator: *operator, left, right },
                    self.knownness(left).join(self.knownness(right)),
                    span,
                    ty,
                )
            }
            Expression::Ternary { condition, yes, no, .. } => {
                let condition = self.lift_expression(condition);
                let yes = self.lift_expression(yes);
                let no = self.lift_expression(no);
                if self.scalar_shape(condition) == ScalarShape::Invalid {
                    return self.opaque_expression(span);
                }
                let ty = if self.scalar_shape(condition) == ScalarShape::Deferred {
                    ValueType::Unknown
                } else if self.expression_type(yes) == self.expression_type(no) {
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
        for step in path.steps.iter().rev() {
            match step {
                AccessStep::Port { port, .. } => {
                    return match &self.hir.ports[port.index].schema {
                        PortSchema::Signal => ValueType::Plain,
                        PortSchema::Bus(id) => ValueType::Bus(*id),
                        PortSchema::Opaque(_) => ValueType::Unknown,
                    };
                }
                AccessStep::Tag { .. } => return ValueType::Plain,
                AccessStep::Index { .. } => {}
            }
        }
        self.symbol_type(path.terminal)
    }

    pub(super) fn access_rank(&self, path: &AccessPath) -> Option<usize> {
        let rank = self.symbol_rank(path.terminal)?;
        let mut indices = 0;
        for step in path.steps.iter().rev() {
            match step {
                AccessStep::Index { .. } => indices += 1,
                AccessStep::Port { .. } => break,
                AccessStep::Tag { .. } => return Some(0),
            }
        }
        rank.checked_sub(indices)
    }

    fn symbol_rank(&self, id: SymbolId) -> Option<usize> {
        let symbol = &self.hir.symbols[id.index];
        if !symbol.shape_checked || symbol.kind == SymbolKind::Parameter {
            return None;
        }
        Some(symbol.rank)
    }

    pub(super) fn expression_rank(&self, id: ExprId) -> Option<usize> {
        let expression = self.hir.expression(id)?;
        match &expression.kind {
            ExprKind::Number(_) | ExprKind::Unary { .. } | ExprKind::Binary { .. } => Some(0),
            ExprKind::Call { .. } => None,
            ExprKind::Access(path) => self.access_rank(path),
            ExprKind::Array(elements) => {
                let Some(first) = elements.first() else { return Some(1) };
                let rank = self.expression_rank(*first)?;
                elements
                    .iter()
                    .all(|id| self.expression_rank(*id) == Some(rank))
                    .then_some(rank + 1)
            }
            ExprKind::Ternary { yes, no, .. } => {
                let rank = self.expression_rank(*yes)?;
                (self.expression_rank(*no) == Some(rank)).then_some(rank)
            }
            ExprKind::Parallel(operand) => self.expression_rank(*operand),
            ExprKind::AnonymousComponent { component, .. } => {
                let target = self.hir.components[component.index].target.as_ref()?;
                let CallTarget::Template(template) = target else { return None };
                self.anonymous_output_shape(*template).map(|(_, rank)| rank)
            }
            ExprKind::Tuple(_) | ExprKind::Opaque(_) => None,
        }
    }

    pub(super) fn check_value_shape(
        &self,
        expected_type: ValueType,
        expected_rank: usize,
        value: ExprId,
    ) -> ShapeCheck {
        if self.deferred_value_shape(value) {
            return ShapeCheck::Unknown;
        }
        let actual_type = self.expression_type(value);
        let actual_rank = self.expression_rank(value);
        if expected_type == ValueType::Unknown || actual_type == ValueType::Unknown {
            return ShapeCheck::Unknown;
        }
        let Some(actual_rank) = actual_rank else { return ShapeCheck::Unknown };
        if matches!(actual_type, ValueType::Component(_)) {
            return ShapeCheck::Invalid(SemanticCode::WrongAssignmentExpression);
        }
        if matches!((expected_type, actual_type), (ValueType::Bus(_), ValueType::Bus(_)))
            && expected_rank != actual_rank
        {
            return ShapeCheck::Invalid(SemanticCode::WrongAssignmentRank);
        }
        if expected_type != actual_type {
            return ShapeCheck::Invalid(SemanticCode::WrongBusAssignment);
        }
        if expected_rank != actual_rank {
            return ShapeCheck::Invalid(SemanticCode::WrongAssignmentRank);
        }
        ShapeCheck::Valid
    }

    fn deferred_value_shape(&self, id: ExprId) -> bool {
        let Some(expression) = self.hir.expression(id) else { return false };
        match &expression.kind {
            ExprKind::Number(_) | ExprKind::Opaque(_) => false,
            ExprKind::Access(path) => {
                let symbol = &self.hir.symbols[path.terminal.index];
                symbol.value_evidence == ValueEvidence::Deferred
                    || symbol.kind == SymbolKind::Parameter
                    || Self::symbolic_indices(path).any(|index| self.deferred_value_shape(index))
            }
            ExprKind::Call { target: CallTarget::Function(_), .. } => true,
            ExprKind::Call { arguments, .. } => {
                arguments.iter().any(|id| self.deferred_value_shape(*id))
            }
            ExprKind::AnonymousComponent { arguments, inputs, .. } => {
                arguments.iter().any(|id| self.deferred_value_shape(*id))
                    || inputs.iter().any(|input| self.deferred_value_shape(input.value))
            }
            ExprKind::Array(values) | ExprKind::Tuple(values) => {
                values.iter().any(|id| self.deferred_value_shape(*id))
            }
            ExprKind::Unary { operand, .. } | ExprKind::Parallel(operand) => {
                self.deferred_value_shape(*operand)
            }
            ExprKind::Binary { left, right, .. } => {
                self.deferred_value_shape(*left) || self.deferred_value_shape(*right)
            }
            ExprKind::Ternary { condition, yes, no } => {
                self.deferred_value_shape(*condition)
                    || self.deferred_value_shape(*yes)
                    || self.deferred_value_shape(*no)
            }
        }
    }

    pub(super) fn scalar_shape(&self, id: ExprId) -> ScalarShape {
        if !self.expression_is_checked(id) {
            return ScalarShape::Invalid;
        }
        let Some(expression) = self.hir.expression(id) else {
            return ScalarShape::Invalid;
        };
        match &expression.kind {
            ExprKind::Access(path)
                if self.hir.symbols[path.terminal.index].kind == SymbolKind::Variable
                    && self.hir.symbols[path.terminal.index].value_evidence
                        == ValueEvidence::Deferred =>
            {
                ScalarShape::Deferred
            }
            ExprKind::Access(path)
                if self.hir.symbols[path.terminal.index].kind == SymbolKind::Parameter =>
            {
                ScalarShape::Deferred
            }
            ExprKind::Call { target: CallTarget::Function(_), .. } => ScalarShape::Deferred,
            ExprKind::Unary { operand, .. } => self.scalar_shape(*operand),
            ExprKind::Binary { left, right, .. } => {
                self.scalar_shape(*left).join(self.scalar_shape(*right))
            }
            ExprKind::Ternary { condition, yes, no } => self
                .scalar_shape(*condition)
                .join(self.scalar_shape(*yes))
                .join(self.scalar_shape(*no)),
            _ if self.expression_type(id) == ValueType::Plain
                && self.expression_rank(id) == Some(0) =>
            {
                ScalarShape::Checked
            }
            _ => ScalarShape::Invalid,
        }
    }

    pub(super) fn equality_shape(&self, left: ExprId, right: ExprId) -> ShapeCheck {
        if !self.expression_is_checked(left) || !self.expression_is_checked(right) {
            return ShapeCheck::Invalid(SemanticCode::WrongAssignmentExpression);
        }
        let ty = self.expression_type(left);
        match ty {
            ValueType::Plain | ValueType::Bus(_) => {
                let Some(rank) = self.expression_rank(left) else { return ShapeCheck::Unknown };
                self.check_value_shape(ty, rank, right)
            }
            ValueType::Unknown => ShapeCheck::Unknown,
            ValueType::Component(_) => ShapeCheck::Invalid(SemanticCode::WrongAssignmentExpression),
        }
    }

    fn opaque_expression(&mut self, span: Span) -> ExprId {
        self.incomplete(span, IncompleteReason::UnknownType);
        self.add_expression(
            ExprKind::Opaque(IncompleteReason::UnknownType),
            Knownness::Opaque,
            span,
            ValueType::Unknown,
        )
    }

    fn anonymous_output_shape(&self, template: TemplateId) -> Option<(ValueType, usize)> {
        let mut outputs = self.hir.templates[template.index]
            .ports
            .iter()
            .filter(|port| self.hir.ports[port.index].direction == Some(PortDirection::Output));
        let port = *outputs.next()?;
        if outputs.next().is_some() {
            return None;
        }
        let port = &self.hir.ports[port.index];
        let ty = match port.schema {
            PortSchema::Signal => ValueType::Plain,
            PortSchema::Bus(id) => ValueType::Bus(id),
            PortSchema::Opaque(_) => return None,
        };
        Some((ty, self.hir.symbols[port.symbol.index].rank))
    }

    pub(super) fn array_type(&self, elements: &[ExprId]) -> ValueType {
        let Some(first) = elements.first() else { return ValueType::Plain };
        let ty = self.expression_type(*first);
        if ty == ValueType::Unknown
            || matches!(ty, ValueType::Component(_))
            || elements.iter().any(|element| self.expression_type(*element) != ty)
        {
            ValueType::Unknown
        } else {
            ty
        }
    }

    pub(super) fn span_key(span: Span) -> (usize, usize, usize) {
        (span.source().index(), span.start(), span.end())
    }

    pub(super) fn lift_anonymous(&mut self, call: &AnonymousCallExpr) -> ExprId {
        let mut target = self.resolve_call(&call.name, DefinitionKind::Template);
        let arguments: Vec<_> =
            call.parameters.iter().map(|value| self.lift_expression(value)).collect();
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
            .map(|(position, input)| self.lift_anonymous_input(template, input, position))
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
        let ty = template
            .filter(|_| valid_inputs)
            .and_then(|template| self.anonymous_output_shape(template))
            .map_or(ValueType::Unknown, |(ty, _)| ty);
        self.add_expression(
            ExprKind::AnonymousComponent { component, arguments, inputs },
            if valid_target && valid_inputs {
                Knownness::WitnessDependent
            } else {
                Knownness::Opaque
            },
            call.span,
            ty,
        )
    }

    pub(super) fn lift_anonymous_input(
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
        let value = self.lift_expression(value);
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
            match self.hir.ports[port.index].schema.clone() {
                PortSchema::Signal => {
                    self.checked_anonymous_port(port, ValueType::Plain, value, span)
                }
                PortSchema::Bus(id) => {
                    self.checked_anonymous_port(port, ValueType::Bus(id), value, span)
                }
                PortSchema::Opaque(reason) => {
                    self.incomplete(span, reason.clone());
                    AnonymousInputTarget::Opaque(reason)
                }
            }
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

    fn checked_anonymous_port(
        &mut self,
        port: crate::hir::PortId,
        expected_type: ValueType,
        value: ExprId,
        span: Span,
    ) -> AnonymousInputTarget {
        let symbol = self.hir.ports[port.index].symbol;
        let rank = self.hir.symbols[symbol.index].rank;
        match self.check_value_shape(expected_type, rank, value) {
            ShapeCheck::Valid => AnonymousInputTarget::Port(port),
            ShapeCheck::Invalid(code) => {
                self.diagnostic(
                    code,
                    Severity::Error,
                    span,
                    "anonymous input value has incompatible type or array rank".into(),
                );
                self.incomplete(span, IncompleteReason::InvalidAssignment);
                AnonymousInputTarget::Opaque(IncompleteReason::InvalidAssignment)
            }
            ShapeCheck::Unknown => {
                self.incomplete(span, IncompleteReason::UnknownType);
                AnonymousInputTarget::Opaque(IncompleteReason::UnknownType)
            }
        }
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

    pub(super) fn lift_mains(&mut self) {
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
                        arguments.iter().map(|value| self.lift_expression(value)).collect();
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
