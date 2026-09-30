use crate::hir::lower::*;

impl Lowerer<'_> {
    pub(super) fn lower_statement(&mut self, statement: &Statement) -> Vec<Effect> {
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

    pub(super) fn lower_local_statement(&mut self, statement: &Statement) -> Vec<Effect> {
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
                if !self.compatible_equality_operands(left, right) {
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

    pub(super) fn lower_control_statement(&mut self, statement: &Statement) -> Vec<Effect> {
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
                if !self.scalar_arithmetic_operand(condition) {
                    return vec![self.opaque(span, IncompleteReason::UnknownType)];
                }
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
                if !self.scalar_arithmetic_operand(condition) {
                    return vec![self.opaque(span, IncompleteReason::UnknownType)];
                }
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
                if !self.scalar_arithmetic_operand(condition) {
                    return vec![self.opaque(span, IncompleteReason::UnknownType)];
                }
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

    pub(super) fn lower_terminal_statement(&mut self, statement: &Statement) -> Vec<Effect> {
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
                let condition = self.lower_expression(condition);
                if !self.scalar_arithmetic_operand(condition) {
                    return vec![self.opaque(span, IncompleteReason::UnknownType)];
                }
                vec![Effect::Assert { condition, span }]
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

    pub(super) fn snapshot_knownness(&self) -> Vec<Knownness> {
        self.hir.symbols.iter().map(|symbol| symbol.knownness).collect()
    }

    pub(super) fn symbolic_indices(path: &AccessPath) -> impl Iterator<Item = ExprId> + '_ {
        path.steps.iter().filter_map(|step| match step {
            AccessStep::Index { index: ArrayIndex::Symbolic(id), .. } => Some(*id),
            AccessStep::Index { index: ArrayIndex::Constant(_), .. }
            | AccessStep::Port { .. }
            | AccessStep::Tag { .. } => None,
        })
    }

    pub(super) fn access_knownness(&self, path: &AccessPath) -> Knownness {
        let mut knownness = self.hir.symbols[path.terminal.index].knownness;
        for id in Self::symbolic_indices(path) {
            knownness = knownness.join(self.knownness(id));
        }
        knownness
    }

    pub(super) fn expression_is_checked(&self, id: ExprId) -> bool {
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

    pub(super) fn loop_condition_is_stable(&self, condition: ExprId, before: &[Knownness]) -> bool {
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

    pub(super) fn restore_knownness(&mut self, snapshot: &[Knownness]) {
        for (symbol, knownness) in self.hir.symbols.iter_mut().zip(snapshot) {
            symbol.knownness = *knownness;
        }
    }

    pub(super) fn join_knownness(&mut self, first: &[Knownness], second: &[Knownness]) {
        for (index, (first, second)) in first.iter().zip(second).enumerate() {
            let current = self.hir.symbols[index].knownness;
            self.hir.symbols[index].knownness = current.join(*first).join(*second);
        }
    }

    pub(super) fn opaque(&mut self, span: Span, reason: IncompleteReason) -> Effect {
        self.incomplete(span, reason.clone());
        Effect::Opaque { reason, span }
    }

    pub(super) fn invalid_assignment(&mut self, span: Span, message: &str) -> Effect {
        self.diagnostic(SemanticCode::InvalidAssignment, Severity::Error, span, message.into());
        self.opaque(span, IncompleteReason::InvalidAssignment)
    }

    pub(super) fn declare(&mut self, name: &Identifier, kind: SymbolKind) -> Option<SymbolId> {
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

    pub(super) fn lower_declaration(&mut self, declaration: &Declaration) -> Vec<Effect> {
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

    pub(super) fn lower_bus_arguments(&mut self, declaration: &Declaration) -> Vec<ExprId> {
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

    pub(super) fn lower_bus_type(
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

    pub(super) fn lower_declared_symbol(
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
        let mut valid_shape = true;
        for dimension in &declared.dimensions {
            let id = self.lower_expression(dimension);
            valid_shape &= self.expect_compile_time(id, dimension.span(), true);
            self.hir.symbols[symbol.index].dimensions.push(id);
        }
        self.hir.symbols[symbol.index].shape_checked = valid_shape;
        if kind == SymbolKind::Component {
            self.components.insert(symbol, self.hir.add_component(symbol, declared.span));
        }
        if self.hir.symbols[symbol.index].tags.is_empty() {
            for tag in tags {
                let id = self.hir.add_symbol(tag.name.clone(), SymbolKind::Tag, tag.span);
                self.hir.symbols[symbol.index].tags.push(id);
            }
        }
        if !valid_shape {
            return vec![self.opaque(declared.span, IncompleteReason::NonCompileTime)];
        }
        let mut effects = vec![Effect::Declaration { symbol, span: declared.span }];
        if let Some((operator, value)) = &declared.initialization {
            effects.push(self.assignment_for_symbol(symbol, *operator, value, declared.span));
        }
        effects
    }

    pub(super) fn lower_tuple_initialization(&mut self, declaration: &Declaration) -> Vec<Effect> {
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

    pub(super) fn bind_predeclared(&mut self, name: &Identifier, symbol: SymbolId) -> bool {
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

    pub(super) fn direction(direction: DirectionSyntax) -> Option<PortDirection> {
        match direction {
            DirectionSyntax::Unspecified => None,
            DirectionSyntax::Before(value) | DirectionSyntax::After(value) => Some(value.direction),
        }
    }

    pub(super) fn assignment_for_symbol(
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

    pub(super) fn lower_assignment(
        &mut self,
        target: &Expression,
        operator: AssignmentOperator,
        value: &Expression,
        span: Span,
    ) -> Effect {
        let Some(path) = self.lower_access(target) else {
            return self.opaque(span, IncompleteReason::InvalidAssignment);
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

    pub(super) fn assignment_effect(
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
        if matches!(
            kind,
            SymbolKind::Variable | SymbolKind::Signal | SymbolKind::Bus | SymbolKind::Tag
        ) {
            let Some(rank) = self.access_rank(&path) else {
                return self.opaque(span, IncompleteReason::UnknownType);
            };
            match self.check_value_shape(self.access_type(&path), rank, value) {
                ShapeCheck::Valid => {}
                ShapeCheck::Invalid(code) => {
                    self.diagnostic(
                        code,
                        Severity::Error,
                        span,
                        "assignment value has incompatible type or array rank".into(),
                    );
                    return self.opaque(span, IncompleteReason::InvalidAssignment);
                }
                ShapeCheck::Unknown => return self.opaque(span, IncompleteReason::UnknownType),
            }
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

    pub(super) fn lower_component_value(&mut self, symbol: SymbolId, value: &Expression) -> ExprId {
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
}
