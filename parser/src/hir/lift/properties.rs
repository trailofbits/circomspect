use std::collections::HashMap;

use crate::hir::lift::{Lifter, ScalarShape, ValueType};
use crate::hir::{
    AccessPath, AccessStep, AnonymousInputTarget, ArrayIndex, CallTarget, Expr, ExprId, ExprKind,
    Knownness, SymbolKind, ValueEvidence,
};

pub(super) trait ExpressionChildren {
    fn for_each_child(&self, visit: impl FnMut(ExprId));
}

impl ExpressionChildren for AccessPath {
    fn for_each_child(&self, mut visit: impl FnMut(ExprId)) {
        for id in symbolic_indices(self) {
            visit(id);
        }
    }
}

pub(super) fn symbolic_indices(path: &AccessPath) -> impl Iterator<Item = ExprId> + '_ {
    path.steps.iter().filter_map(|step| match step {
        AccessStep::Index { index: ArrayIndex::Symbolic(id), .. } => Some(*id),
        AccessStep::Index { index: ArrayIndex::Constant(_), .. }
        | AccessStep::Port { .. }
        | AccessStep::Tag { .. } => None,
    })
}

impl ExpressionChildren for ExprKind {
    fn for_each_child(&self, mut visit: impl FnMut(ExprId)) {
        match self {
            Self::Number(_) | Self::Opaque(_) => {}
            Self::Access(path) => path.for_each_child(visit),
            Self::Call { arguments, .. } | Self::Array(arguments) | Self::Tuple(arguments) => {
                for id in arguments {
                    visit(*id);
                }
            }
            Self::AnonymousComponent { arguments, inputs, .. } => {
                for id in arguments {
                    visit(*id);
                }
                for input in inputs {
                    visit(input.value);
                }
            }
            Self::Unary { operand, .. } | Self::Parallel(operand) => visit(*operand),
            Self::Binary { left, right, .. } => {
                visit(*left);
                visit(*right);
            }
            Self::Ternary { condition, yes, no } => {
                visit(*condition);
                visit(*yes);
                visit(*no);
            }
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ExpressionProperties {
    pub(super) checked: bool,
    pub(super) rank: Option<usize>,
    pub(super) scalar: ScalarShape,
    pub(super) value_evidence: ValueEvidence,
    pub(super) compile_time: bool,
    pub(super) witness_only: bool,
}

impl Default for ExpressionProperties {
    fn default() -> Self {
        Self {
            checked: false,
            rank: None,
            scalar: ScalarShape::Invalid,
            value_evidence: ValueEvidence::Checked,
            compile_time: false,
            witness_only: false,
        }
    }
}

struct ChildProperties {
    checked: bool,
    scalar: ScalarShape,
    value_evidence: ValueEvidence,
    compile_time: bool,
    witness_only: bool,
}

impl Default for ChildProperties {
    fn default() -> Self {
        Self {
            checked: true,
            scalar: ScalarShape::Checked,
            value_evidence: ValueEvidence::Checked,
            compile_time: true,
            witness_only: true,
        }
    }
}

enum Frame {
    Enter(ExprId),
    Finish(ExprId),
}

/// One immutable lifting state. Dropping the query discards every computed property.
pub(super) struct ExpressionQuery<'query, 'source> {
    lifter: &'query Lifter<'source>,
    completed: HashMap<ExprId, ExpressionProperties>,
    #[cfg(test)]
    pub(super) child_visits: usize,
    #[cfg(test)]
    node_completions: usize,
}

impl<'query, 'source> ExpressionQuery<'query, 'source> {
    pub(super) fn new(lifter: &'query Lifter<'source>) -> Self {
        Self {
            lifter,
            completed: HashMap::new(),
            #[cfg(test)]
            child_visits: 0,
            #[cfg(test)]
            node_completions: 0,
        }
    }

    pub(super) fn get(&mut self, root: ExprId) -> ExpressionProperties {
        let mut pending = vec![Frame::Enter(root)];
        while let Some(frame) = pending.pop() {
            match frame {
                Frame::Enter(id) => {
                    if self.completed.contains_key(&id) {
                        continue;
                    }
                    let Some(expression) = self.lifter.hir.expression(id) else {
                        self.completed.insert(id, ExpressionProperties::default());
                        #[cfg(test)]
                        {
                            self.node_completions += 1;
                        }
                        continue;
                    };
                    pending.push(Frame::Finish(id));
                    expression.kind.for_each_child(|child| {
                        #[cfg(test)]
                        {
                            self.child_visits += 1;
                        }
                        pending.push(Frame::Enter(child));
                    });
                }
                Frame::Finish(id) => {
                    let properties = self.summarize(id);
                    self.completed.insert(id, properties);
                    #[cfg(test)]
                    {
                        self.node_completions += 1;
                    }
                }
            }
        }
        self.lookup(root)
    }

    #[cfg(test)]
    pub(super) fn completed_nodes(&self) -> usize {
        self.node_completions
    }

    fn lookup(&self, id: ExprId) -> ExpressionProperties {
        self.completed.get(&id).copied().unwrap_or_default()
    }

    fn summarize(&self, id: ExprId) -> ExpressionProperties {
        let Some(expression) = self.lifter.hir.expression(id) else {
            return ExpressionProperties::default();
        };
        let mut children = ChildProperties::default();
        expression.kind.for_each_child(|id| {
            let child = self.lookup(id);
            children.checked &= child.checked;
            children.scalar = children.scalar.join(child.scalar);
            children.value_evidence = children.value_evidence.join(child.value_evidence);
            children.compile_time &= child.compile_time;
            children.witness_only &= child.witness_only;
        });
        let checked = self.checked(expression, children.checked);
        let rank = self.rank(&expression.kind);
        ExpressionProperties {
            checked,
            rank,
            scalar: self.scalar(expression, checked, rank, children.scalar),
            value_evidence: self.value_evidence(&expression.kind, children.value_evidence),
            compile_time: Self::compile_time(expression, children.compile_time),
            witness_only: Self::witness_only(&expression.kind, children.witness_only),
        }
    }

    fn checked(&self, expression: &Expr, children: bool) -> bool {
        if !children {
            return false;
        }
        match &expression.kind {
            ExprKind::Call { target, .. } => {
                let (CallTarget::Function(_) | CallTarget::Template(_)) = target else {
                    return false;
                };
                true
            }
            ExprKind::AnonymousComponent { component, inputs, .. } => {
                let Some(CallTarget::Template(_)) =
                    &self.lifter.hir.components[component.index].target
                else {
                    return false;
                };
                expression.knownness != Knownness::Opaque
                    && inputs.iter().all(|input| {
                        let AnonymousInputTarget::Port(_) = input.target else { return false };
                        true
                    })
            }
            ExprKind::Opaque(_) => false,
            ExprKind::Number(_)
            | ExprKind::Access(_)
            | ExprKind::Array(_)
            | ExprKind::Tuple(_)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Ternary { .. }
            | ExprKind::Parallel(_) => true,
        }
    }

    fn rank(&self, kind: &ExprKind) -> Option<usize> {
        match kind {
            ExprKind::Number(_) | ExprKind::Unary { .. } | ExprKind::Binary { .. } => Some(0),
            ExprKind::Access(path) => self.lifter.access_rank(path),
            ExprKind::Array(elements) => {
                let Some(first) = elements.first() else { return Some(1) };
                let rank = self.lookup(*first).rank?;
                elements.iter().all(|id| self.lookup(*id).rank == Some(rank)).then_some(rank + 1)
            }
            ExprKind::Ternary { yes, no, .. } => {
                let rank = self.lookup(*yes).rank?;
                (self.lookup(*no).rank == Some(rank)).then_some(rank)
            }
            ExprKind::Parallel(operand) => self.lookup(*operand).rank,
            ExprKind::AnonymousComponent { component, .. } => {
                let target = self.lifter.hir.components[component.index].target.as_ref()?;
                let CallTarget::Template(template) = target else { return None };
                self.lifter.anonymous_output_shape(*template).map(|(_, rank)| rank)
            }
            ExprKind::Call { .. } | ExprKind::Tuple(_) | ExprKind::Opaque(_) => None,
        }
    }

    fn scalar(
        &self,
        expression: &Expr,
        checked: bool,
        rank: Option<usize>,
        children: ScalarShape,
    ) -> ScalarShape {
        if !checked {
            return ScalarShape::Invalid;
        }
        match &expression.kind {
            ExprKind::Access(path) => {
                let symbol = &self.lifter.hir.symbols[path.terminal.index];
                if symbol.kind == SymbolKind::Parameter
                    || (symbol.kind == SymbolKind::Variable
                        && symbol.value_evidence == ValueEvidence::Deferred)
                {
                    return ScalarShape::Deferred;
                }
            }
            ExprKind::Call { target: CallTarget::Function(_), .. } => return ScalarShape::Deferred,
            ExprKind::Unary { .. } | ExprKind::Binary { .. } | ExprKind::Ternary { .. } => {
                return children;
            }
            ExprKind::Number(_)
            | ExprKind::Call { .. }
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Array(_)
            | ExprKind::Tuple(_)
            | ExprKind::Parallel(_)
            | ExprKind::Opaque(_) => {}
        }
        if self.lifter.expression_type(expression.id) == ValueType::Plain && rank == Some(0) {
            ScalarShape::Checked
        } else {
            ScalarShape::Invalid
        }
    }

    fn value_evidence(&self, kind: &ExprKind, children: ValueEvidence) -> ValueEvidence {
        match kind {
            ExprKind::Number(_) | ExprKind::Opaque(_) => ValueEvidence::Checked,
            ExprKind::Access(path) => {
                let symbol = &self.lifter.hir.symbols[path.terminal.index];
                if symbol.kind == SymbolKind::Parameter {
                    ValueEvidence::Deferred
                } else {
                    symbol.value_evidence.join(children)
                }
            }
            ExprKind::Call { target: CallTarget::Function(_), .. } => ValueEvidence::Deferred,
            ExprKind::Call { .. }
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Array(_)
            | ExprKind::Tuple(_)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Ternary { .. }
            | ExprKind::Parallel(_) => children,
        }
    }

    fn compile_time(expression: &Expr, children: bool) -> bool {
        match &expression.kind {
            ExprKind::Number(_) => true,
            ExprKind::Access(_) => expression.knownness.is_compile_time() && children,
            ExprKind::Call { target: CallTarget::Function(_), .. }
            | ExprKind::Array(_)
            | ExprKind::Tuple(_)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Ternary { .. } => children,
            ExprKind::Call { .. }
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Parallel(_)
            | ExprKind::Opaque(_) => false,
        }
    }

    fn witness_only(kind: &ExprKind, children: bool) -> bool {
        match kind {
            ExprKind::Number(_)
            | ExprKind::Access(_)
            | ExprKind::Array(_)
            | ExprKind::Tuple(_)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Ternary { .. } => children,
            ExprKind::Call { .. }
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Parallel(_)
            | ExprKind::Opaque(_) => false,
        }
    }
}

impl Lifter<'_> {
    pub(super) fn expression_properties(&self, id: ExprId) -> ExpressionProperties {
        ExpressionQuery::new(self).get(id)
    }
}
