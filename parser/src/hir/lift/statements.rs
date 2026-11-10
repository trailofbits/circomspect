use crate::hir::lift::properties::{symbolic_indices, ExpressionChildren};
use crate::hir::lift::{
    AccessPath, AccessStep, ArrayIndex, AssignmentOperator, BTreeSet, BlockId, BusTarget,
    CallTarget, ControlGuard, Declaration, DeclarationKind, DeclaredSymbol, DefinitionKind,
    DefinitionRef, DirectionSyntax, Effect, ExprId, ExprKind, Expression, Identifier,
    IncompleteReason, Knownness, Lifter, LogArgument, PortDirection, ScalarShape, SemanticCode,
    Severity, ShapeCheck, Span, Statement, SymbolId, SymbolKind, SymbolSnapshot, ValueEvidence,
    ValueType, TemplateInvocation, ForLoop, PostfixOperator,
};

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
        if let ExprKind::Access(path) = expression {
            if symbols.contains(&path.root) {
                return true;
            }
        }
        let mut invalid = false;
        expression.for_each_child(|id| invalid |= expressions.contains(&id));
        invalid
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
                        | Effect::DeferredAssert { .. }
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
        let (target, value, operator, span) = match effect {
            Effect::VariableAssignment { target, value, operator, span }
            | Effect::DeferredVariableAssignment { target, value, operator, span } => {
                (target, *value, *operator, *span)
            }
            Effect::ComponentInstantiation { target, value, span } => {
                (target, *value, AssignmentOperator::Assign, *span)
            }
            Effect::WitnessAssignment { target, value, span } => {
                (target, *value, AssignmentOperator::Witness, *span)
            }
            Effect::ConstraintAssignment { target, value, span } => {
                (target, *value, AssignmentOperator::Constraint, *span)
            }
            Effect::EqualityConstraint { left, right, span } => {
                return if expressions.contains(left) || expressions.contains(right) {
                    Some(Effect::OpaqueEquality { left: *left, right: *right, reason, span: *span })
                } else {
                    None
                };
            }
            Effect::Update { target, span, .. } => {
                return Self::path_depends_on_invalid(target, symbols, expressions)
                    .then_some(Effect::Opaque { reason, span: *span });
            }
            Effect::If { condition, span, .. }
            | Effect::While { condition, span, .. }
            | Effect::For { condition, span, .. }
            | Effect::Assert { condition, span }
            | Effect::DeferredAssert { condition, span } => {
                return expressions
                    .contains(condition)
                    .then_some(Effect::Opaque { reason, span: *span });
            }
            Effect::Return { value, span }
            | Effect::AnonymousComponent { expression: value, span } => {
                return expressions
                    .contains(value)
                    .then_some(Effect::Opaque { reason, span: *span });
            }
            Effect::Log { values, span } => {
                return values
                    .iter()
                    .any(|id| expressions.contains(id))
                    .then_some(Effect::Opaque { reason, span: *span });
            }
            Effect::Declaration { .. }
            | Effect::OpaqueAssignment { .. }
            | Effect::OpaqueEquality { .. }
            | Effect::Block(_)
            | Effect::Opaque { .. } => return None,
        };
        if !Self::path_depends_on_invalid(target, symbols, expressions)
            && !expressions.contains(&value)
        {
            return None;
        }
        Some(Effect::OpaqueAssignment { target: target.clone(), value, operator, reason, span })
    }

    pub(super) fn lift_statement(&mut self, statement: &Statement) -> Vec<Effect> {
        let span = statement.span();
        let effect = match statement {
            Statement::Block(body) => {
                let block = self.hir.add_block(body.span);
                self.lift_block_into(&body.statements, block, true);
                Effect::Block(block)
            }
            Statement::Declaration(declaration) => return self.lift_declaration(declaration),
            Statement::Assignment { target, operator, value, .. } => {
                self.lift_assignment(target, *operator, value, span)
            }
            Statement::PostfixUpdate { target, operator, .. } => {
                self.lift_postfix_update(target, *operator, span)
            }
            Statement::Constraint { left, right, .. } => self.lift_equality(left, right, span),
            Statement::If { condition, then_branch, else_branch, .. } => {
                self.lift_if(condition, then_branch, else_branch.as_deref(), span)
            }
            Statement::For { initializer, condition, step, body, .. } => {
                self.lift_for(ForLoop { initializer, condition, step, body, span })
            }
            Statement::While { condition, body, .. } => self.lift_while(condition, body, span),
            Statement::Return { value, .. } => self.lift_return(value, span),
            Statement::Assert { condition, .. } => self.lift_assert(condition, span),
            Statement::Log { arguments, .. } => {
                let mut values = Vec::new();
                for argument in arguments {
                    match argument {
                        LogArgument::String { .. } => {}
                        LogArgument::Expression(value) => values.push(self.lift_expression(value)),
                    }
                }
                Effect::Log { values, span }
            }
            Statement::AnonymousCall { call, .. } => {
                let expression = self.lift_anonymous(call);
                Effect::AnonymousComponent { expression, span }
            }
            Statement::Error { .. } => self.opaque(span, IncompleteReason::Syntax),
        };
        vec![effect]
    }

    fn lift_postfix_update(
        &mut self,
        target: &Expression,
        operator: PostfixOperator,
        span: Span,
    ) -> Effect {
        let Some(path) = self.lift_access(target) else {
            return self.opaque(span, IncompleteReason::InvalidAssignment);
        };
        let kind = self.hir.symbols[path.root.index].kind;
        if !Self::local_value_target(kind) {
            return self.invalid_assignment(span, "postfix update requires a variable");
        }
        if !Self::symbolic_indices(&path).all(|id| self.expression_is_checked(id)) {
            return self.opaque(span, IncompleteReason::UnknownType);
        }
        if kind == SymbolKind::Parameter {
            self.incomplete(span, IncompleteReason::UnknownType);
        }
        let knownness = self.access_knownness(&path);
        self.hir.symbols[path.terminal.index].knownness = knownness;
        Effect::Update { target: path, operator, span }
    }

    fn lift_equality(&mut self, left: &Expression, right: &Expression, span: Span) -> Effect {
        if let Some(DefinitionRef::Function(_)) = self.current_definition {
            self.diagnostic(
                SemanticCode::ConstraintInFunction,
                Severity::Error,
                span,
                "a function cannot generate constraints".into(),
            );
            return self
                .opaque(span, IncompleteReason::Unsupported("constraint in function".into()));
        }
        let left = self.lift_expression(left);
        let right = self.lift_expression(right);
        match self.equality_shape(left, right) {
            ShapeCheck::Valid => Effect::EqualityConstraint { left, right, span },
            ShapeCheck::Unknown => {
                let reason = IncompleteReason::UnknownType;
                self.incomplete(span, reason.clone());
                Effect::OpaqueEquality { left, right, reason, span }
            }
            ShapeCheck::Invalid(_) => self.opaque(span, IncompleteReason::UnknownType),
        }
    }

    fn lift_if(
        &mut self,
        condition: &Expression,
        then_branch: &Statement,
        else_branch: Option<&Statement>,
        span: Span,
    ) -> Effect {
        let condition = self.lift_expression(condition);
        let before = SymbolSnapshot::capture(&self.hir);
        let then_block = self.lift_branch(then_branch);
        let after_then = SymbolSnapshot::capture(&self.hir);
        before.install(&mut self.hir);
        let else_block = else_branch.map(|branch| self.lift_branch(branch));
        let after_else = SymbolSnapshot::capture(&self.hir);
        after_then.join(&after_else).install(&mut self.hir);
        let guard = match self.control_guard(condition) {
            Ok(ControlGuard::WitnessOnly)
                if !self.branch_is_witness_only(then_block)
                    || else_block.is_some_and(|id| !self.branch_is_witness_only(id)) =>
            {
                return self.opaque(span, IncompleteReason::NonCompileTime);
            }
            Ok(guard) => guard,
            Err(reason) => return self.opaque(span, reason),
        };
        Effect::If { condition, guard, then_block, else_block, span }
    }

    fn lift_for(&mut self, for_loop: ForLoop<'_>) -> Effect {
        let ForLoop { initializer, condition, step, body, span } = for_loop;
        self.scopes.enter();
        let initializer_block = self.hir.add_block(initializer.span());
        self.lift_block_into(std::slice::from_ref(initializer), initializer_block, false);
        let before_loop = SymbolSnapshot::capture(&self.hir);
        let condition = self.lift_expression(condition);
        let body = self.lift_branch(body);
        let after_body = SymbolSnapshot::capture(&self.hir);
        let step = self.lift_branch(step);
        let after_step = SymbolSnapshot::capture(&self.hir);
        let stable_condition = self.loop_condition_is_stable(condition, &before_loop);
        before_loop.join(&after_body).join(&after_step).install(&mut self.hir);
        self.scopes.leave();
        let guard = match self.control_guard(condition) {
            Ok(ControlGuard::WitnessOnly) => {
                return self.opaque(span, IncompleteReason::NonCompileTime);
            }
            Ok(guard) => guard,
            Err(reason) => return self.opaque(span, reason),
        };
        if !stable_condition {
            return self.opaque(span, IncompleteReason::NonCompileTime);
        }
        Effect::For { initializer: initializer_block, condition, guard, step, body, span }
    }

    fn lift_while(&mut self, condition: &Expression, body: &Statement, span: Span) -> Effect {
        let before = SymbolSnapshot::capture(&self.hir);
        let condition = self.lift_expression(condition);
        let body = self.lift_branch(body);
        let after_body = SymbolSnapshot::capture(&self.hir);
        let stable_condition = self.loop_condition_is_stable(condition, &before);
        before.join(&after_body).install(&mut self.hir);
        let guard = match self.control_guard(condition) {
            Ok(ControlGuard::WitnessOnly) => {
                return self.opaque(span, IncompleteReason::NonCompileTime);
            }
            Ok(guard) => guard,
            Err(reason) => return self.opaque(span, reason),
        };
        if !stable_condition {
            return self.opaque(span, IncompleteReason::NonCompileTime);
        }
        Effect::While { condition, guard, body, span }
    }

    fn lift_return(&mut self, value: &Expression, span: Span) -> Effect {
        let Some(DefinitionRef::Function(_)) = self.current_definition else {
            self.diagnostic(
                SemanticCode::TemplateReturn,
                Severity::Error,
                span,
                "return is only valid in a function".into(),
            );
            return self
                .opaque(span, IncompleteReason::Unsupported("return outside function".into()));
        };
        Effect::Return { value: self.lift_expression(value), span }
    }

    fn lift_assert(&mut self, condition: &Expression, span: Span) -> Effect {
        let condition = self.lift_expression(condition);
        match self.scalar_shape(condition) {
            ScalarShape::Checked => Effect::Assert { condition, span },
            ScalarShape::Deferred => Effect::DeferredAssert { condition, span },
            ScalarShape::Invalid => self.opaque(span, IncompleteReason::UnknownType),
        }
    }

    fn control_guard(&self, condition: ExprId) -> Result<ControlGuard, IncompleteReason> {
        let properties = self.expression_properties(condition);
        let shape = properties.scalar;
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
            Knownness::Opaque if shape == ScalarShape::Deferred && properties.compile_time => {
                Ok(ControlGuard::DeferredScalar)
            }
            Knownness::WitnessDependent | Knownness::Opaque => Err(IncompleteReason::UnknownType),
        }
    }

    pub(super) fn provisionally_compile_time(&self, id: ExprId) -> bool {
        self.expression_properties(id).compile_time
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
            Effect::DeferredAssert { .. }
            | Effect::ComponentInstantiation { .. }
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

    pub(super) fn expression_is_witness_only(&self, id: ExprId) -> bool {
        self.expression_properties(id).witness_only
    }

    pub(super) fn symbolic_indices(path: &AccessPath) -> impl Iterator<Item = ExprId> + '_ {
        symbolic_indices(path)
    }

    pub(super) fn access_knownness(&self, path: &AccessPath) -> Knownness {
        let mut knownness = self.hir.symbols[path.terminal.index].knownness;
        for id in Self::symbolic_indices(path) {
            knownness = knownness.join(self.knownness(id));
        }
        knownness
    }

    pub(super) fn expression_is_checked(&self, id: ExprId) -> bool {
        self.expression_properties(id).checked
    }

    pub(super) fn loop_condition_is_stable(
        &self,
        condition: ExprId,
        before: &SymbolSnapshot,
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
                }
                ExprKind::Unary { .. }
                | ExprKind::Parallel(_)
                | ExprKind::Binary { .. }
                | ExprKind::Ternary { .. }
                | ExprKind::Array(_)
                | ExprKind::Tuple(_)
                | ExprKind::Number(_) => {}
                ExprKind::Call { .. }
                | ExprKind::AnonymousComponent { .. }
                | ExprKind::Opaque(_) => return false,
            }
            expression.kind.for_each_child(|child| pending.push(child));
        }
        true
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
            if Self::local_value_target(kind) {
                return self.unknown_shape_assignment(path, kind, operator, value, span);
            }
            return self.opaque(span, IncompleteReason::UnknownType);
        }
        if kind == SymbolKind::Parameter {
            return self.unknown_shape_assignment(path, kind, operator, value, span);
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
            (
                SymbolKind::Variable | SymbolKind::Component | SymbolKind::Tag,
                AssignmentOperator::Assign,
            )
            | (
                SymbolKind::Variable,
                AssignmentOperator::Add
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
                | AssignmentOperator::BitXor,
            ) => {
                if let SymbolKind::Variable | SymbolKind::Tag = kind {
                    self.update_assignment_knownness(&path, operator, value);
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
        if Self::local_value_target(kind) {
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
        if Self::local_value_target(kind)
            && self.provisionally_compile_time(value)
            && Self::symbolic_indices(&path).all(|index| self.provisionally_compile_time(index))
        {
            self.update_assignment_knownness(&path, operator, value);
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

    fn update_assignment_knownness(
        &mut self,
        path: &AccessPath,
        operator: AssignmentOperator,
        value: ExprId,
    ) {
        let current = self.hir.symbols[path.terminal.index].knownness;
        let next = self.knownness(value);
        self.hir.symbols[path.terminal.index].knownness =
            if operator == AssignmentOperator::Assign && path.steps.is_empty() {
                next
            } else {
                current.join(next).join(self.access_knownness(path))
            };
    }

    fn local_value_target(kind: SymbolKind) -> bool {
        match kind {
            SymbolKind::Variable | SymbolKind::Parameter => true,
            SymbolKind::Signal | SymbolKind::Component | SymbolKind::Bus | SymbolKind::Tag => false,
        }
    }

    pub(super) fn lift_component_value(&mut self, symbol: SymbolId, value: &Expression) -> ExprId {
        let Some(invocation) = TemplateInvocation::from_expression(value) else {
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
        let span = invocation.span;
        let arguments: Vec<_> =
            invocation.arguments.iter().map(|value| self.lift_expression(value)).collect();
        let target = self.resolve_call(invocation.name, DefinitionKind::Template);
        let mut target = self.check_template_invocation(target, &arguments, span);
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
        if let Some(span) = invocation.parallel_span {
            self.add_expression(ExprKind::Parallel(call), Knownness::Opaque, span, ty)
        } else {
            call
        }
    }
}
