use crate::hir::lift::*;

impl Lifter<'_> {
    fn path_depends_on_invalid(
        path: &AccessPath,
        symbols: &BTreeSet<SymbolId>,
        expressions: &BTreeSet<ExprId>,
    ) -> bool {
        symbols.contains(&path.root)
            || path.steps.iter().any(|step| match step {
                AccessStep::Index { index: ArrayIndex::Symbolic(id), .. } => {
                    expressions.contains(id)
                }
                AccessStep::Index { index: ArrayIndex::Constant(_), .. }
                | AccessStep::Port { .. }
                | AccessStep::Tag { .. } => false,
            })
    }

    fn expression_depends_on_invalid(
        expression: &ExprKind,
        symbols: &BTreeSet<SymbolId>,
        expressions: &BTreeSet<ExprId>,
    ) -> bool {
        match expression {
            ExprKind::Access(path) => Self::path_depends_on_invalid(path, symbols, expressions),
            ExprKind::Call { arguments, .. }
            | ExprKind::Array(arguments)
            | ExprKind::Tuple(arguments) => arguments.iter().any(|id| expressions.contains(id)),
            ExprKind::AnonymousComponent { arguments, inputs, .. } => {
                arguments.iter().any(|id| expressions.contains(id))
                    || inputs.iter().any(|input| expressions.contains(&input.value))
            }
            ExprKind::Unary { operand, .. } | ExprKind::Parallel(operand) => {
                expressions.contains(operand)
            }
            ExprKind::Binary { left, right, .. } => {
                expressions.contains(left) || expressions.contains(right)
            }
            ExprKind::Ternary { condition, yes, no } => {
                expressions.contains(condition)
                    || expressions.contains(yes)
                    || expressions.contains(no)
            }
            ExprKind::Number(_) | ExprKind::Opaque(_) => false,
        }
    }

    fn invalid_component_dependencies(
        &self,
        component: SymbolId,
    ) -> (BTreeSet<SymbolId>, BTreeSet<ExprId>) {
        let mut symbols = BTreeSet::from([component]);
        let mut expressions = BTreeSet::new();
        loop {
            let before = (symbols.len(), expressions.len());
            for block in &self.hir.blocks {
                for effect in &block.effects {
                    match effect {
                        Effect::ComponentInstantiation { target, value, .. } => {
                            if target.root == component {
                                expressions.insert(*value);
                            }
                            if expressions.contains(value)
                                || Self::path_depends_on_invalid(target, &symbols, &expressions)
                            {
                                symbols.insert(target.root);
                            }
                        }
                        Effect::VariableAssignment { target, value, .. }
                        | Effect::DeferredVariableAssignment { target, value, .. }
                        | Effect::WitnessAssignment { target, value, .. }
                        | Effect::ConstraintAssignment { target, value, .. }
                        | Effect::OpaqueAssignment { target, value, .. } => {
                            if expressions.contains(value)
                                || Self::path_depends_on_invalid(target, &symbols, &expressions)
                            {
                                symbols.insert(target.root);
                            }
                        }
                        Effect::Update { target, .. } => {
                            if Self::path_depends_on_invalid(target, &symbols, &expressions) {
                                symbols.insert(target.root);
                            }
                        }
                        Effect::Declaration { .. }
                        | Effect::EqualityConstraint { .. }
                        | Effect::OpaqueEquality { .. }
                        | Effect::If { .. }
                        | Effect::While { .. }
                        | Effect::For { .. }
                        | Effect::Return { .. }
                        | Effect::Assert { .. }
                        | Effect::Log { .. }
                        | Effect::AnonymousComponent { .. }
                        | Effect::Block(_)
                        | Effect::Opaque { .. } => {}
                    }
                }
            }
            for expression in &self.hir.expressions {
                if Self::expression_depends_on_invalid(&expression.kind, &symbols, &expressions) {
                    expressions.insert(expression.id);
                }
            }
            if before == (symbols.len(), expressions.len()) {
                return (symbols, expressions);
            }
        }
    }

    fn invalidate_component_evidence(&mut self, symbol: SymbolId) {
        let (symbols, expressions) = self.invalid_component_dependencies(symbol);
        self.invalid_symbols.extend(symbols.iter().copied());
        for id in &expressions {
            self.hir.expressions[id.index].kind =
                ExprKind::Opaque(IncompleteReason::InvalidAssignment);
            self.expression_types[id.index] = ValueType::Unknown;
        }
        for block in &mut self.hir.blocks {
            for effect in &mut block.effects {
                if let Some(opaque) = Self::opaque_invalid_effect(effect, &symbols, &expressions) {
                    *effect = opaque;
                }
            }
        }
    }

    fn opaque_invalid_effect(
        effect: &Effect,
        symbols: &BTreeSet<SymbolId>,
        expressions: &BTreeSet<ExprId>,
    ) -> Option<Effect> {
        let reason = IncompleteReason::InvalidAssignment;
        match effect {
            Effect::DeferredVariableAssignment { target, value, operator, span } => {
                if !Self::path_depends_on_invalid(target, symbols, expressions)
                    && !expressions.contains(value)
                {
                    return None;
                }
                Some(Effect::OpaqueAssignment {
                    target: target.clone(),
                    value: *value,
                    operator: *operator,
                    reason,
                    span: *span,
                })
            }
            Effect::VariableAssignment { target, value, span, .. }
            | Effect::ComponentInstantiation { target, value, span }
            | Effect::WitnessAssignment { target, value, span }
            | Effect::ConstraintAssignment { target, value, span } => {
                if !Self::path_depends_on_invalid(target, symbols, expressions)
                    && !expressions.contains(value)
                {
                    return None;
                }
                let operator = match effect {
                    Effect::WitnessAssignment { .. } => AssignmentOperator::Witness,
                    Effect::ConstraintAssignment { .. } => AssignmentOperator::Constraint,
                    Effect::VariableAssignment { operator, .. } => *operator,
                    Effect::ComponentInstantiation { .. } => AssignmentOperator::Assign,
                    Effect::Declaration { .. }
                    | Effect::DeferredVariableAssignment { .. }
                    | Effect::OpaqueAssignment { .. }
                    | Effect::EqualityConstraint { .. }
                    | Effect::OpaqueEquality { .. }
                    | Effect::Update { .. }
                    | Effect::If { .. }
                    | Effect::While { .. }
                    | Effect::For { .. }
                    | Effect::Return { .. }
                    | Effect::Assert { .. }
                    | Effect::Log { .. }
                    | Effect::AnonymousComponent { .. }
                    | Effect::Block(_)
                    | Effect::Opaque { .. } => return None,
                };
                Some(Effect::OpaqueAssignment {
                    target: target.clone(),
                    value: *value,
                    operator,
                    reason,
                    span: *span,
                })
            }
            Effect::EqualityConstraint { left, right, span } => {
                if expressions.contains(left) || expressions.contains(right) {
                    Some(Effect::OpaqueEquality { left: *left, right: *right, reason, span: *span })
                } else {
                    None
                }
            }
            Effect::Update { target, span, .. } => {
                Self::path_depends_on_invalid(target, symbols, expressions)
                    .then_some(Effect::Opaque { reason, span: *span })
            }
            Effect::If { condition, span, .. }
            | Effect::While { condition, span, .. }
            | Effect::For { condition, span, .. }
            | Effect::Assert { condition, span } => {
                expressions.contains(condition).then_some(Effect::Opaque { reason, span: *span })
            }
            Effect::Return { value, span }
            | Effect::AnonymousComponent { expression: value, span } => {
                expressions.contains(value).then_some(Effect::Opaque { reason, span: *span })
            }
            Effect::Log { values, span } => values
                .iter()
                .any(|id| expressions.contains(id))
                .then_some(Effect::Opaque { reason, span: *span }),
            Effect::Declaration { .. }
            | Effect::OpaqueAssignment { .. }
            | Effect::OpaqueEquality { .. }
            | Effect::Block(_)
            | Effect::Opaque { .. } => None,
        }
    }

    pub(super) fn lift_statement(&mut self, statement: &Statement) -> Vec<Effect> {
        match statement {
            Statement::Block(_)
            | Statement::Declaration(_)
            | Statement::Assignment { .. }
            | Statement::PostfixUpdate { .. }
            | Statement::Constraint { .. } => self.lift_local_statement(statement),
            Statement::If { .. } | Statement::For { .. } | Statement::While { .. } => {
                self.lift_control_statement(statement)
            }
            Statement::Return { .. }
            | Statement::Assert { .. }
            | Statement::Log { .. }
            | Statement::AnonymousCall { .. }
            | Statement::Error { .. } => self.lift_terminal_statement(statement),
        }
    }

    pub(super) fn lift_local_statement(&mut self, statement: &Statement) -> Vec<Effect> {
        let span = statement.span();
        match statement {
            Statement::Block(_) => vec![Effect::Block(self.lift_branch(statement))],
            Statement::Declaration(declaration) => self.lift_declaration(declaration),
            Statement::Assignment { target, operator, value, .. } => {
                vec![self.lift_assignment(target, *operator, value, span)]
            }
            Statement::PostfixUpdate { target, operator, .. } => {
                let Some(path) = self.lift_access(target) else {
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
                let left = self.lift_expression(left);
                let right = self.lift_expression(right);
                match self.equality_shape(left, right) {
                    ShapeCheck::Valid => vec![Effect::EqualityConstraint { left, right, span }],
                    ShapeCheck::Unknown => {
                        let reason = IncompleteReason::UnknownType;
                        self.incomplete(span, reason.clone());
                        vec![Effect::OpaqueEquality { left, right, reason, span }]
                    }
                    ShapeCheck::Invalid(_) => {
                        vec![self.opaque(span, IncompleteReason::UnknownType)]
                    }
                }
            }
            _ => {
                let reason = IncompleteReason::Unsupported("local statement form".into());
                vec![self.opaque(span, reason)]
            }
        }
    }

    pub(super) fn lift_control_statement(&mut self, statement: &Statement) -> Vec<Effect> {
        let span = statement.span();
        match statement {
            Statement::If { condition, then_branch, else_branch, .. } => {
                let condition = self.lift_expression(condition);
                let before = self.snapshot_symbol_state();
                let then_block = self.lift_branch(then_branch);
                let after_then = self.snapshot_symbol_state();
                self.restore_symbol_state(&before);
                let else_block = else_branch.as_ref().map(|branch| self.lift_branch(branch));
                let after_else = self.snapshot_symbol_state();
                self.join_symbol_state(&after_then, &after_else);
                let guard = match self.control_guard(condition) {
                    Ok(ControlGuard::WitnessOnly)
                        if !self.branch_is_witness_only(then_block)
                            || else_block.is_some_and(|id| !self.branch_is_witness_only(id)) =>
                    {
                        return vec![self.opaque(span, IncompleteReason::NonCompileTime)];
                    }
                    Ok(guard) => guard,
                    Err(reason) => return vec![self.opaque(span, reason)],
                };
                vec![Effect::If { condition, guard, then_block, else_block, span }]
            }
            Statement::For { initializer, condition, step, body, .. } => {
                self.scopes.enter();
                let initializer_block = self.hir.add_block(initializer.span());
                self.lift_block_into(std::slice::from_ref(initializer), initializer_block, false);
                let before_loop = self.snapshot_symbol_state();
                let condition = self.lift_expression(condition);
                let body = self.lift_branch(body);
                let after_body = self.snapshot_symbol_state();
                let step = self.lift_branch(step);
                let stable_condition = self.loop_condition_is_stable(condition, &before_loop);
                self.join_symbol_state(&before_loop, &after_body);
                self.scopes.leave();
                let guard = match self.control_guard(condition) {
                    Ok(ControlGuard::WitnessOnly) => {
                        return vec![self.opaque(span, IncompleteReason::NonCompileTime)];
                    }
                    Ok(guard) => guard,
                    Err(reason) => return vec![self.opaque(span, reason)],
                };
                if !stable_condition {
                    return vec![self.opaque(span, IncompleteReason::NonCompileTime)];
                }
                vec![Effect::For {
                    initializer: initializer_block,
                    condition,
                    guard,
                    step,
                    body,
                    span,
                }]
            }
            Statement::While { condition, body, .. } => {
                let before = self.snapshot_symbol_state();
                let condition = self.lift_expression(condition);
                let body = self.lift_branch(body);
                let stable_condition = self.loop_condition_is_stable(condition, &before);
                self.join_symbol_state(&before, &before);
                let guard = match self.control_guard(condition) {
                    Ok(ControlGuard::WitnessOnly) => {
                        return vec![self.opaque(span, IncompleteReason::NonCompileTime)];
                    }
                    Ok(guard) => guard,
                    Err(reason) => return vec![self.opaque(span, reason)],
                };
                if !stable_condition {
                    return vec![self.opaque(span, IncompleteReason::NonCompileTime)];
                }
                vec![Effect::While { condition, guard, body, span }]
            }
            _ => {
                vec![self
                    .opaque(span, IncompleteReason::Unsupported("control statement form".into()))]
            }
        }
    }

    fn control_guard(&self, condition: ExprId) -> Result<ControlGuard, IncompleteReason> {
        let shape = self.scalar_shape(condition);
        if shape == ScalarShape::Invalid {
            return Err(IncompleteReason::UnknownType);
        }
        match self.knownness(condition) {
            Knownness::Constant | Knownness::ParameterDependent => match shape {
                ScalarShape::Checked => Ok(ControlGuard::CheckedCompileTime),
                ScalarShape::Deferred => Ok(ControlGuard::DeferredScalar),
                ScalarShape::Invalid => Err(IncompleteReason::UnknownType),
            },
            Knownness::WitnessDependent if shape == ScalarShape::Checked => {
                Ok(ControlGuard::WitnessOnly)
            }
            Knownness::WitnessDependent => Err(IncompleteReason::UnknownType),
            Knownness::Opaque
                if shape == ScalarShape::Deferred && self.provisionally_compile_time(condition) =>
            {
                Ok(ControlGuard::DeferredScalar)
            }
            Knownness::Opaque => Err(IncompleteReason::UnknownType),
        }
    }

    fn provisionally_compile_time(&self, id: ExprId) -> bool {
        let Some(expression) = self.hir.expression(id) else { return false };
        match &expression.kind {
            ExprKind::Number(_) => true,
            ExprKind::Access(path) => {
                expression.knownness.is_compile_time()
                    && Self::symbolic_indices(path)
                        .all(|index| self.provisionally_compile_time(index))
            }
            ExprKind::Call { target: CallTarget::Function(_), arguments } => {
                arguments.iter().all(|id| self.provisionally_compile_time(*id))
            }
            ExprKind::Array(values) | ExprKind::Tuple(values) => {
                values.iter().all(|id| self.provisionally_compile_time(*id))
            }
            ExprKind::Unary { operand, .. } => self.provisionally_compile_time(*operand),
            ExprKind::Binary { left, right, .. } => {
                self.provisionally_compile_time(*left) && self.provisionally_compile_time(*right)
            }
            ExprKind::Ternary { condition, yes, no } => {
                self.provisionally_compile_time(*condition)
                    && self.provisionally_compile_time(*yes)
                    && self.provisionally_compile_time(*no)
            }
            ExprKind::Call { .. }
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Parallel(_)
            | ExprKind::Opaque(_) => false,
        }
    }

    fn branch_is_witness_only(&self, block: BlockId) -> bool {
        self.hir.blocks[block.index].effects.iter().all(|effect| match effect {
            Effect::Declaration { symbol, .. } => {
                self.hir.symbols[symbol.index].kind == SymbolKind::Variable
            }
            Effect::VariableAssignment { target, value, .. }
            | Effect::WitnessAssignment { target, value, .. } => {
                Self::symbolic_indices(target).all(|id| self.expression_is_witness_only(id))
                    && self.expression_is_witness_only(*value)
            }
            Effect::Update { target, .. } => {
                Self::symbolic_indices(target).all(|id| self.expression_is_witness_only(id))
            }
            Effect::Return { value, .. } | Effect::Assert { condition: value, .. } => {
                self.expression_is_witness_only(*value)
            }
            Effect::Log { values, .. } => {
                values.iter().all(|id| self.expression_is_witness_only(*id))
            }
            Effect::Block(child) => self.branch_is_witness_only(*child),
            Effect::ComponentInstantiation { .. }
            | Effect::DeferredVariableAssignment { .. }
            | Effect::ConstraintAssignment { .. }
            | Effect::EqualityConstraint { .. }
            | Effect::If { .. }
            | Effect::While { .. }
            | Effect::For { .. }
            | Effect::AnonymousComponent { .. }
            | Effect::OpaqueAssignment { .. }
            | Effect::OpaqueEquality { .. }
            | Effect::Opaque { .. } => false,
        })
    }

    fn expression_is_witness_only(&self, id: ExprId) -> bool {
        let Some(expression) = self.hir.expression(id) else { return false };
        match &expression.kind {
            ExprKind::Number(_) => true,
            ExprKind::Access(path) => {
                Self::symbolic_indices(path).all(|index| self.expression_is_witness_only(index))
            }
            ExprKind::Array(values) | ExprKind::Tuple(values) => {
                values.iter().all(|id| self.expression_is_witness_only(*id))
            }
            ExprKind::Unary { operand, .. } => self.expression_is_witness_only(*operand),
            ExprKind::Binary { left, right, .. } => {
                self.expression_is_witness_only(*left) && self.expression_is_witness_only(*right)
            }
            ExprKind::Ternary { condition, yes, no } => {
                self.expression_is_witness_only(*condition)
                    && self.expression_is_witness_only(*yes)
                    && self.expression_is_witness_only(*no)
            }
            ExprKind::Call { .. }
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Parallel(_)
            | ExprKind::Opaque(_) => false,
        }
    }

    pub(super) fn lift_terminal_statement(&mut self, statement: &Statement) -> Vec<Effect> {
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
                vec![Effect::Return { value: self.lift_expression(value), span }]
            }
            Statement::Assert { condition, .. } => {
                let condition = self.lift_expression(condition);
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
                        LogArgument::Expression(value) => Some(self.lift_expression(value)),
                    })
                    .collect();
                vec![Effect::Log { values, span }]
            }
            Statement::AnonymousCall { call, .. } => {
                let expression = self.lift_anonymous(call);
                vec![Effect::AnonymousComponent { expression, span }]
            }
            Statement::Error { .. } => vec![self.opaque(span, IncompleteReason::Syntax)],
            _ => {
                vec![self
                    .opaque(span, IncompleteReason::Unsupported("terminal statement form".into()))]
            }
        }
    }

    pub(super) fn snapshot_symbol_state(&self) -> Vec<SymbolState> {
        self.hir
            .symbols
            .iter()
            .map(|symbol| SymbolState {
                knownness: symbol.knownness,
                value_evidence: symbol.value_evidence,
            })
            .collect()
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

    pub(super) fn loop_condition_is_stable(
        &self,
        condition: ExprId,
        before: &[SymbolState],
    ) -> bool {
        let mut pending = vec![condition];
        while let Some(id) = pending.pop() {
            let Some(expression) = self.hir.expression(id) else { return false };
            match &expression.kind {
                ExprKind::Access(path) => {
                    let Some(initial) = before.get(path.terminal.index) else { return false };
                    if self.hir.symbols[path.terminal.index].knownness != initial.knownness
                        || self.hir.symbols[path.terminal.index].value_evidence
                            != initial.value_evidence
                    {
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

    pub(super) fn restore_symbol_state(&mut self, snapshot: &[SymbolState]) {
        for (symbol, state) in self.hir.symbols.iter_mut().zip(snapshot) {
            symbol.knownness = state.knownness;
            symbol.value_evidence = state.value_evidence;
        }
    }

    pub(super) fn join_symbol_state(&mut self, first: &[SymbolState], second: &[SymbolState]) {
        for (index, (first, second)) in first.iter().zip(second).enumerate() {
            let symbol = &mut self.hir.symbols[index];
            symbol.knownness = symbol.knownness.join(first.knownness).join(second.knownness);
            symbol.value_evidence =
                symbol.value_evidence.join(first.value_evidence).join(second.value_evidence);
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

    pub(super) fn lift_declaration(&mut self, declaration: &Declaration) -> Vec<Effect> {
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
        let bus_arguments = self.lift_bus_arguments(declaration);
        let bus_type = self.lift_bus_type(declaration, &bus_arguments);
        let mut effects = Vec::new();
        for declared in &declaration.symbols {
            effects.extend(self.lift_declared_symbol(
                declared,
                kind,
                bus_type.clone(),
                &bus_arguments,
                tags,
            ));
        }
        effects.extend(self.lift_tuple_initialization(declaration));
        effects
    }

    pub(super) fn lift_bus_arguments(&mut self, declaration: &Declaration) -> Vec<ExprId> {
        let DeclarationKind::Bus { arguments, .. } = &declaration.kind else { return Vec::new() };
        arguments
            .values()
            .iter()
            .map(|argument| {
                let id = self.lift_expression(argument);
                self.expect_compile_time(id, argument.span(), false);
                id
            })
            .collect()
    }

    pub(super) fn lift_bus_type(
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

    pub(super) fn lift_declared_symbol(
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
            let id = self.lift_expression(dimension);
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

    pub(super) fn lift_tuple_initialization(&mut self, declaration: &Declaration) -> Vec<Effect> {
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
            self.lift_component_value(symbol, value)
        } else {
            self.lift_expression(value)
        };
        self.assignment_effect(path, kind, operator, value, span)
    }

    pub(super) fn lift_assignment(
        &mut self,
        target: &Expression,
        operator: AssignmentOperator,
        value: &Expression,
        span: Span,
    ) -> Effect {
        let Some(path) = self.lift_access(target) else {
            return self.opaque(span, IncompleteReason::InvalidAssignment);
        };
        let kind = self.hir.symbols[path.terminal.index].kind;
        let value = if kind == SymbolKind::Component {
            self.lift_component_value(path.root, value)
        } else {
            self.lift_expression(value)
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
            if kind == SymbolKind::Variable {
                return self.unknown_shape_assignment(path, kind, operator, value, span);
            }
            return self.opaque(span, IncompleteReason::UnknownType);
        }
        if matches!(
            kind,
            SymbolKind::Variable | SymbolKind::Signal | SymbolKind::Bus | SymbolKind::Tag
        ) {
            let shape = self.access_rank(&path).map_or(ShapeCheck::Unknown, |rank| {
                self.check_value_shape(self.access_type(&path), rank, value)
            });
            match shape {
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
                ShapeCheck::Unknown => {
                    return self.unknown_shape_assignment(path, kind, operator, value, span);
                }
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
                    Effect::VariableAssignment { target: path, value, operator, span }
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

    fn unknown_shape_assignment(
        &mut self,
        path: AccessPath,
        kind: SymbolKind,
        operator: AssignmentOperator,
        value: ExprId,
        span: Span,
    ) -> Effect {
        self.incomplete(span, IncompleteReason::UnknownType);
        if kind == SymbolKind::Variable {
            match operator {
                AssignmentOperator::Witness
                | AssignmentOperator::Constraint
                | AssignmentOperator::ReverseWitness
                | AssignmentOperator::ReverseConstraint => {
                    return self.invalid_assignment(
                        span,
                        "assignment operator is invalid for target kind",
                    );
                }
                AssignmentOperator::Assign
                | AssignmentOperator::Add
                | AssignmentOperator::Subtract
                | AssignmentOperator::Multiply
                | AssignmentOperator::Divide
                | AssignmentOperator::IntegerDivide
                | AssignmentOperator::Modulo
                | AssignmentOperator::Power
                | AssignmentOperator::ShiftLeft
                | AssignmentOperator::ShiftRight
                | AssignmentOperator::BitAnd
                | AssignmentOperator::BitOr
                | AssignmentOperator::BitXor => {}
            }
        }
        if kind == SymbolKind::Variable
            && self.provisionally_compile_time(value)
            && Self::symbolic_indices(&path).all(|index| self.provisionally_compile_time(index))
        {
            let current = self.hir.symbols[path.terminal.index].knownness;
            let next = self.knownness(value);
            self.hir.symbols[path.terminal.index].knownness =
                if operator == AssignmentOperator::Assign && path.steps.is_empty() {
                    next
                } else {
                    current.join(next).join(self.access_knownness(&path))
                };
            self.hir.symbols[path.terminal.index].value_evidence = ValueEvidence::Deferred;
            return Effect::DeferredVariableAssignment { target: path, value, operator, span };
        }
        Effect::OpaqueAssignment {
            target: path,
            value,
            operator,
            reason: IncompleteReason::UnknownType,
            span,
        }
    }

    pub(super) fn lift_component_value(&mut self, symbol: SymbolId, value: &Expression) -> ExprId {
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
        let arguments: Vec<_> = arguments.iter().map(|value| self.lift_expression(value)).collect();
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
        if let Some(component) = self.components.get(&symbol).copied() {
            let previous = self.hir.components[component.index].target.as_ref();
            let already_invalid = match previous {
                Some(CallTarget::Opaque { reason: IncompleteReason::InvalidAssignment }) => true,
                Some(_) | None => false,
            };
            if already_invalid {
                target = CallTarget::Opaque { reason: IncompleteReason::InvalidAssignment };
            } else if previous.is_some_and(|old| old != &target) {
                self.diagnostic(
                    SemanticCode::InvalidAssignment,
                    Severity::Error,
                    span,
                    "all instances of a component must use the same template".into(),
                );
                self.incomplete(span, IncompleteReason::InvalidAssignment);
                self.invalidate_component_evidence(symbol);
                target = CallTarget::Opaque { reason: IncompleteReason::InvalidAssignment };
            }
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
