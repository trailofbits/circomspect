//! Shared expression traversal for dependency and liveness providers.

use parser::hir::{AccessPath, AccessStep, ArrayIndex, ExprId, ExprKind, HirProject};
use parser::new_frontend::{BinaryOperator, UnaryOperator};

/// Visits accesses guaranteed to be evaluated by a supported scalar expression.
pub trait VisitDefiniteAccesses {
    fn visit_definite_accesses(&self, hir: &HirProject, visit: &mut impl FnMut(&AccessPath));
}

impl VisitDefiniteAccesses for ExprId {
    fn visit_definite_accesses(&self, hir: &HirProject, visit: &mut impl FnMut(&AccessPath)) {
        let Some(expression) = hir.expression(*self) else { return };
        match &expression.kind {
            ExprKind::Access(path) => visit(path),
            ExprKind::Unary { operator: UnaryOperator::Negate, operand }
            | ExprKind::Parallel(operand) => operand.visit_definite_accesses(hir, visit),
            ExprKind::Binary {
                operator: BinaryOperator::Add | BinaryOperator::Subtract | BinaryOperator::Multiply,
                left,
                right,
            } => {
                left.visit_definite_accesses(hir, visit);
                right.visit_definite_accesses(hir, visit);
            }
            ExprKind::Ternary { condition, .. } => condition.visit_definite_accesses(hir, visit),
            ExprKind::Number(_)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Call { .. }
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Array(_)
            | ExprKind::Tuple(_)
            | ExprKind::Opaque(_) => {}
        }
    }
}

/// Visits every access below a HIR expression and reports whether traversal
/// was complete. Unknown expressions cannot prove an empty dependency set.
pub trait VisitAccesses {
    fn visit_accesses(&self, hir: &HirProject, visit: &mut impl FnMut(&AccessPath)) -> bool;
}

impl VisitAccesses for AccessPath {
    fn visit_accesses(&self, hir: &HirProject, visit: &mut impl FnMut(&AccessPath)) -> bool {
        visit(self);
        let mut complete = true;
        for step in &self.steps {
            if let AccessStep::Index { index: ArrayIndex::Symbolic(expression), .. } = step {
                complete &= expression.visit_accesses(hir, visit);
            }
        }
        complete
    }
}

impl VisitAccesses for ExprId {
    fn visit_accesses(&self, hir: &HirProject, visit: &mut impl FnMut(&AccessPath)) -> bool {
        let Some(expression) = hir.expression(*self) else { return false };
        match &expression.kind {
            ExprKind::Number(_) => true,
            ExprKind::Access(path) => path.visit_accesses(hir, visit),
            ExprKind::Unary { operand, .. } | ExprKind::Parallel(operand) => {
                operand.visit_accesses(hir, visit)
            }
            ExprKind::Binary { left, right, .. } => {
                let left_complete = left.visit_accesses(hir, visit);
                let right_complete = right.visit_accesses(hir, visit);
                left_complete && right_complete
            }
            ExprKind::Ternary { condition, yes, no } => {
                let condition_complete = condition.visit_accesses(hir, visit);
                let yes_complete = yes.visit_accesses(hir, visit);
                let no_complete = no.visit_accesses(hir, visit);
                condition_complete && yes_complete && no_complete
            }
            ExprKind::Array(items) | ExprKind::Tuple(items) => {
                let mut complete = true;
                for item in items {
                    complete &= item.visit_accesses(hir, visit);
                }
                complete
            }
            ExprKind::Call { arguments, .. } => {
                for argument in arguments {
                    argument.visit_accesses(hir, visit);
                }
                false
            }
            ExprKind::AnonymousComponent { arguments, inputs, .. } => {
                for argument in arguments {
                    argument.visit_accesses(hir, visit);
                }
                for input in inputs {
                    input.value.visit_accesses(hir, visit);
                }
                false
            }
            ExprKind::Opaque(_) => false,
        }
    }
}
