use crate::hir::lift::{Lifter, ScalarShape, ValueType};
use crate::hir::{
    AnonymousInputTarget, CallTarget, ExprId, ExprKind, Knownness, SymbolKind, ValueEvidence,
};

// Independent recursive policy oracle. Production uses a query-local iterative fold.
impl Lifter<'_> {
    pub(super) fn reference_expression_is_checked(&self, id: ExprId) -> bool {
        let Some(expression) = self.hir.expression(id) else { return false };
        match &expression.kind {
            ExprKind::Number(_) => true,
            ExprKind::Access(path) => {
                reference_indices(path).all(|id| self.reference_expression_is_checked(id))
            }
            ExprKind::Call { target, arguments } => {
                if let CallTarget::Function(_) | CallTarget::Template(_) = target {
                    arguments.iter().all(|id| self.reference_expression_is_checked(*id))
                } else {
                    false
                }
            }
            ExprKind::AnonymousComponent { component, arguments, inputs } => {
                let target = self.hir.components[component.index].target.as_ref();
                let Some(CallTarget::Template(_)) = target else { return false };
                expression.knownness != Knownness::Opaque
                    && arguments.iter().all(|id| self.reference_expression_is_checked(*id))
                    && inputs.iter().all(|input| {
                        let AnonymousInputTarget::Port(_) = input.target else { return false };
                        self.reference_expression_is_checked(input.value)
                    })
            }
            ExprKind::Array(values) | ExprKind::Tuple(values) => {
                values.iter().all(|id| self.reference_expression_is_checked(*id))
            }
            ExprKind::Unary { operand, .. } | ExprKind::Parallel(operand) => {
                self.reference_expression_is_checked(*operand)
            }
            ExprKind::Binary { left, right, .. } => {
                self.reference_expression_is_checked(*left)
                    && self.reference_expression_is_checked(*right)
            }
            ExprKind::Ternary { condition, yes, no } => {
                self.reference_expression_is_checked(*condition)
                    && self.reference_expression_is_checked(*yes)
                    && self.reference_expression_is_checked(*no)
            }
            ExprKind::Opaque(_) => false,
        }
    }

    pub(super) fn reference_expression_rank(&self, id: ExprId) -> Option<usize> {
        let expression = self.hir.expression(id)?;
        match &expression.kind {
            ExprKind::Number(_) | ExprKind::Unary { .. } | ExprKind::Binary { .. } => Some(0),
            ExprKind::Access(path) => self.access_rank(path),
            ExprKind::Array(elements) => {
                let Some(first) = elements.first() else { return Some(1) };
                let rank = self.reference_expression_rank(*first)?;
                elements
                    .iter()
                    .all(|id| self.reference_expression_rank(*id) == Some(rank))
                    .then_some(rank + 1)
            }
            ExprKind::Ternary { yes, no, .. } => {
                let rank = self.reference_expression_rank(*yes)?;
                (self.reference_expression_rank(*no) == Some(rank)).then_some(rank)
            }
            ExprKind::Parallel(operand) => self.reference_expression_rank(*operand),
            ExprKind::AnonymousComponent { component, .. } => {
                let target = self.hir.components[component.index].target.as_ref()?;
                let CallTarget::Template(template) = target else { return None };
                self.anonymous_output_shape(*template).map(|(_, rank)| rank)
            }
            ExprKind::Call { .. } | ExprKind::Tuple(_) | ExprKind::Opaque(_) => None,
        }
    }

    pub(super) fn reference_scalar_shape(&self, id: ExprId) -> ScalarShape {
        if !self.reference_expression_is_checked(id) {
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
            ExprKind::Unary { operand, .. } => self.reference_scalar_shape(*operand),
            ExprKind::Binary { left, right, .. } => {
                self.reference_scalar_shape(*left).join(self.reference_scalar_shape(*right))
            }
            ExprKind::Ternary { condition, yes, no } => self
                .reference_scalar_shape(*condition)
                .join(self.reference_scalar_shape(*yes))
                .join(self.reference_scalar_shape(*no)),
            ExprKind::Number(_)
            | ExprKind::Access(_)
            | ExprKind::Call { .. }
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Array(_)
            | ExprKind::Tuple(_)
            | ExprKind::Parallel(_)
            | ExprKind::Opaque(_) => {
                if self.expression_type(id) == ValueType::Plain
                    && self.reference_expression_rank(id) == Some(0)
                {
                    ScalarShape::Checked
                } else {
                    ScalarShape::Invalid
                }
            }
        }
    }

    pub(super) fn reference_deferred_value_shape(&self, id: ExprId) -> bool {
        let Some(expression) = self.hir.expression(id) else { return false };
        match &expression.kind {
            ExprKind::Number(_) | ExprKind::Opaque(_) => false,
            ExprKind::Access(path) => {
                let symbol = &self.hir.symbols[path.terminal.index];
                symbol.value_evidence == ValueEvidence::Deferred
                    || symbol.kind == SymbolKind::Parameter
                    || reference_indices(path)
                        .any(|index| self.reference_deferred_value_shape(index))
            }
            ExprKind::Call { target: CallTarget::Function(_), .. } => true,
            ExprKind::Call { arguments, .. } => {
                arguments.iter().any(|id| self.reference_deferred_value_shape(*id))
            }
            ExprKind::AnonymousComponent { arguments, inputs, .. } => {
                arguments.iter().any(|id| self.reference_deferred_value_shape(*id))
                    || inputs.iter().any(|input| self.reference_deferred_value_shape(input.value))
            }
            ExprKind::Array(values) | ExprKind::Tuple(values) => {
                values.iter().any(|id| self.reference_deferred_value_shape(*id))
            }
            ExprKind::Unary { operand, .. } | ExprKind::Parallel(operand) => {
                self.reference_deferred_value_shape(*operand)
            }
            ExprKind::Binary { left, right, .. } => {
                self.reference_deferred_value_shape(*left)
                    || self.reference_deferred_value_shape(*right)
            }
            ExprKind::Ternary { condition, yes, no } => {
                self.reference_deferred_value_shape(*condition)
                    || self.reference_deferred_value_shape(*yes)
                    || self.reference_deferred_value_shape(*no)
            }
        }
    }

    pub(super) fn reference_provisionally_compile_time(&self, id: ExprId) -> bool {
        let Some(expression) = self.hir.expression(id) else { return false };
        match &expression.kind {
            ExprKind::Number(_) => true,
            ExprKind::Access(path) => {
                expression.knownness.is_compile_time()
                    && reference_indices(path)
                        .all(|index| self.reference_provisionally_compile_time(index))
            }
            ExprKind::Call { target: CallTarget::Function(_), arguments } => {
                arguments.iter().all(|id| self.reference_provisionally_compile_time(*id))
            }
            ExprKind::Array(values) | ExprKind::Tuple(values) => {
                values.iter().all(|id| self.reference_provisionally_compile_time(*id))
            }
            ExprKind::Unary { operand, .. } => self.reference_provisionally_compile_time(*operand),
            ExprKind::Binary { left, right, .. } => {
                self.reference_provisionally_compile_time(*left)
                    && self.reference_provisionally_compile_time(*right)
            }
            ExprKind::Ternary { condition, yes, no } => {
                self.reference_provisionally_compile_time(*condition)
                    && self.reference_provisionally_compile_time(*yes)
                    && self.reference_provisionally_compile_time(*no)
            }
            ExprKind::Call { .. }
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Parallel(_)
            | ExprKind::Opaque(_) => false,
        }
    }

    pub(super) fn reference_expression_is_witness_only(&self, id: ExprId) -> bool {
        let Some(expression) = self.hir.expression(id) else { return false };
        match &expression.kind {
            ExprKind::Number(_) => true,
            ExprKind::Access(path) => reference_indices(path)
                .all(|index| self.reference_expression_is_witness_only(index)),
            ExprKind::Array(values) | ExprKind::Tuple(values) => {
                values.iter().all(|id| self.reference_expression_is_witness_only(*id))
            }
            ExprKind::Unary { operand, .. } => self.reference_expression_is_witness_only(*operand),
            ExprKind::Binary { left, right, .. } => {
                self.reference_expression_is_witness_only(*left)
                    && self.reference_expression_is_witness_only(*right)
            }
            ExprKind::Ternary { condition, yes, no } => {
                self.reference_expression_is_witness_only(*condition)
                    && self.reference_expression_is_witness_only(*yes)
                    && self.reference_expression_is_witness_only(*no)
            }
            ExprKind::Call { .. }
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Parallel(_)
            | ExprKind::Opaque(_) => false,
        }
    }
}

fn reference_indices(path: &crate::hir::AccessPath) -> impl Iterator<Item = ExprId> + '_ {
    path.steps.iter().filter_map(|step| match step {
        crate::hir::AccessStep::Index { index: crate::hir::ArrayIndex::Symbolic(id), .. } => {
            Some(*id)
        }
        crate::hir::AccessStep::Index { index: crate::hir::ArrayIndex::Constant(_), .. }
        | crate::hir::AccessStep::Port { .. }
        | crate::hir::AccessStep::Tag { .. } => None,
    })
}
