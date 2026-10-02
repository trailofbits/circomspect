//! Shared expression traversal for dependency and liveness providers.

use parser::hir::{AccessPath, AccessStep, ArrayIndex, ExprId, ExprKind, HirProject};

/// Visits every access below a HIR expression and reports whether traversal
/// was complete. Unknown expressions cannot prove an empty dependency set.
pub trait VisitAccesses {
    fn visit_accesses_with(
        &self,
        hir: &HirProject,
        resolved_call: &dyn Fn(ExprId) -> bool,
        visit: &mut impl FnMut(&AccessPath),
    ) -> bool;

    fn visit_accesses(&self, hir: &HirProject, visit: &mut impl FnMut(&AccessPath)) -> bool {
        self.visit_accesses_with(hir, &|_| false, visit)
    }
}

impl VisitAccesses for AccessPath {
    fn visit_accesses_with(
        &self,
        hir: &HirProject,
        resolved_call: &dyn Fn(ExprId) -> bool,
        visit: &mut impl FnMut(&AccessPath),
    ) -> bool {
        visit(self);
        let mut complete = true;
        for step in &self.steps {
            if let AccessStep::Index { index: ArrayIndex::Symbolic(expression), .. } = step {
                complete &= expression.visit_accesses_with(hir, resolved_call, visit);
            }
        }
        complete
    }
}

impl VisitAccesses for ExprId {
    fn visit_accesses_with(
        &self,
        hir: &HirProject,
        resolved_call: &dyn Fn(ExprId) -> bool,
        visit: &mut impl FnMut(&AccessPath),
    ) -> bool {
        let Some(expression) = hir.expression(*self) else { return false };
        match &expression.kind {
            ExprKind::Number(_) => true,
            ExprKind::Access(path) => path.visit_accesses_with(hir, resolved_call, visit),
            ExprKind::Unary { operand, .. } | ExprKind::Parallel(operand) => {
                operand.visit_accesses_with(hir, resolved_call, visit)
            }
            ExprKind::Binary { left, right, .. } => {
                let left_complete = left.visit_accesses_with(hir, resolved_call, visit);
                let right_complete = right.visit_accesses_with(hir, resolved_call, visit);
                left_complete && right_complete
            }
            ExprKind::Ternary { condition, yes, no } => {
                let condition_complete = condition.visit_accesses_with(hir, resolved_call, visit);
                let yes_complete = yes.visit_accesses_with(hir, resolved_call, visit);
                let no_complete = no.visit_accesses_with(hir, resolved_call, visit);
                condition_complete && yes_complete && no_complete
            }
            ExprKind::Array(items) | ExprKind::Tuple(items) => {
                let mut complete = true;
                for item in items {
                    complete &= item.visit_accesses_with(hir, resolved_call, visit);
                }
                complete
            }
            ExprKind::Call { arguments, .. } => {
                let mut complete = true;
                for argument in arguments {
                    complete &= argument.visit_accesses_with(hir, resolved_call, visit);
                }
                complete && resolved_call(*self)
            }
            ExprKind::AnonymousComponent { arguments, inputs, .. } => {
                for argument in arguments {
                    argument.visit_accesses_with(hir, resolved_call, visit);
                }
                for input in inputs {
                    input.value.visit_accesses_with(hir, resolved_call, visit);
                }
                false
            }
            ExprKind::Opaque(_) => false,
        }
    }
}
