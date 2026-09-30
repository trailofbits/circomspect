use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::NodeId;
use abstract_interpretation::lattice::Lattice;
use abstract_interpretation::solver::{DataflowAnalysis, Transfer, TransferOutcome};
use parser::hir::{ExprId, ExprKind, HirProject, SymbolId, SymbolKind};
use parser::new_frontend::{BinaryOperator, UnaryOperator};

use crate::hir_cfg::{CfgEdge, CfgNode, CfgNodeKind, DefinitionCfg, EdgeKind};

use super::field::{FieldContext, FieldValue};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ForwardState {
    Unreachable,
    Reached {
        variables: BTreeMap<SymbolId, FieldValue>,
        may_constraints: BTreeSet<NodeId>,
        must_constraints: BTreeSet<NodeId>,
    },
}

impl ForwardState {
    pub fn boundary() -> Self {
        Self::Reached {
            variables: BTreeMap::new(),
            may_constraints: BTreeSet::new(),
            must_constraints: BTreeSet::new(),
        }
    }

    pub fn variables(&self) -> Option<&BTreeMap<SymbolId, FieldValue>> {
        let Self::Reached { variables, .. } = self else { return None };
        Some(variables)
    }

    pub fn constraints(&self) -> Option<(&BTreeSet<NodeId>, &BTreeSet<NodeId>)> {
        let Self::Reached { may_constraints, must_constraints, .. } = self else { return None };
        Some((may_constraints, must_constraints))
    }
}

impl Lattice for ForwardState {
    fn bottom() -> Self {
        Self::Unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unreachable, _) => true,
            (Self::Reached { .. }, Self::Unreachable) => false,
            (
                Self::Reached {
                    variables: left,
                    may_constraints: left_may,
                    must_constraints: left_must,
                },
                Self::Reached {
                    variables: right,
                    may_constraints: right_may,
                    must_constraints: right_must,
                },
            ) => {
                right.iter().all(|(key, value)| left.get(key) == Some(value))
                    && left_may.is_subset(right_may)
                    && left_must.is_superset(right_must)
            }
        }
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        if let Self::Unreachable = other {
            return false;
        }
        if let Self::Unreachable = self {
            *self = other.clone();
            return true;
        }
        let old = self.clone();
        let (
            Self::Reached {
                variables: left,
                may_constraints: left_may,
                must_constraints: left_must,
            },
            Self::Reached {
                variables: right,
                may_constraints: right_may,
                must_constraints: right_must,
            },
        ) = (&mut *self, other)
        else {
            return false;
        };
        left.retain(|key, value| right.get(key) == Some(value));
        left_may.extend(right_may);
        left_must.retain(|site| right_must.contains(site));
        *self != old
    }
}

pub struct ForwardAnalysis<'a> {
    pub hir: &'a HirProject,
    pub field: &'a FieldContext,
}

impl DataflowAnalysis<DefinitionCfg> for ForwardAnalysis<'_> {
    type State = ForwardState;
    type Reason = String;

    fn boundary(&self, _: NodeId) -> Self::State {
        ForwardState::boundary()
    }
}

impl Transfer<ForwardAnalysis<'_>, ForwardState, String> for CfgNode {
    fn apply(
        &self,
        analysis: &ForwardAnalysis<'_>,
        input: &ForwardState,
    ) -> TransferOutcome<ForwardState, String> {
        let mut output = input.clone();
        let ForwardState::Reached { variables, may_constraints, must_constraints } = &mut output
        else {
            return TransferOutcome::Known(output);
        };
        match &self.kind {
            CfgNodeKind::Evaluate(id) => {
                let Some(expression) = analysis.hir.expression(*id) else {
                    return TransferOutcome::Opaque {
                        provisional: output,
                        reason: "missing expression".into(),
                    };
                };
                if let ExprKind::Opaque(reason) = &expression.kind {
                    return TransferOutcome::Opaque {
                        provisional: output,
                        reason: format!("{reason:?}"),
                    };
                }
                if let ExprKind::AnonymousComponent { .. } = &expression.kind {
                    return TransferOutcome::Opaque {
                        provisional: output,
                        reason: "external component summary".into(),
                    };
                }
            }
            CfgNodeKind::Assignment { target, value } => {
                if analysis
                    .hir
                    .symbol(target.root)
                    .is_some_and(|symbol| symbol.kind == SymbolKind::Variable)
                {
                    if let Some(value) =
                        eval_expression(analysis.hir, analysis.field, *value, variables)
                    {
                        variables.insert(target.root, value);
                    } else {
                        variables.remove(&target.root);
                    }
                }
            }
            CfgNodeKind::Constraint { .. } => {
                may_constraints.insert(self.id);
                must_constraints.insert(self.id);
            }
            CfgNodeKind::Opaque(reason) => {
                return TransferOutcome::Opaque {
                    provisional: output,
                    reason: format!("{reason:?}"),
                };
            }
            CfgNodeKind::Instantiate { .. } => {
                return TransferOutcome::Opaque {
                    provisional: output,
                    reason: "external component summary".into(),
                };
            }
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::LoopHeader
            | CfgNodeKind::Branch(_)
            | CfgNodeKind::Witness { .. }
            | CfgNodeKind::Declaration
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Assert { .. }
            | CfgNodeKind::Log => {}
        }
        TransferOutcome::Known(output)
    }
}

impl Transfer<ForwardAnalysis<'_>, ForwardState, String> for CfgEdge {
    fn apply(
        &self,
        analysis: &ForwardAnalysis<'_>,
        input: &ForwardState,
    ) -> TransferOutcome<ForwardState, String> {
        let Some(condition) = self.condition else {
            return TransferOutcome::Known(input.clone());
        };
        let Some(variables) = input.variables() else {
            return TransferOutcome::Known(ForwardState::Unreachable);
        };
        let Some(value) = eval_expression(analysis.hir, analysis.field, condition, variables)
        else {
            return TransferOutcome::Known(input.clone());
        };
        let truth = !analysis.field.is_zero(&value);
        let taken = match self.kind {
            EdgeKind::True => truth,
            EdgeKind::False => !truth,
            EdgeKind::Normal | EdgeKind::Loop | EdgeKind::Return => true,
        };
        TransferOutcome::Known(if taken { input.clone() } else { ForwardState::Unreachable })
    }
}

/// Evaluate only proven compile-time expressions in a concrete variable environment.
pub fn eval_expression(
    hir: &HirProject,
    field: &FieldContext,
    id: ExprId,
    variables: &BTreeMap<SymbolId, FieldValue>,
) -> Option<FieldValue> {
    let expression = hir.expression(id)?;
    match &expression.kind {
        ExprKind::Number(text) => field.parse(text),
        ExprKind::Access(path) if path.steps.is_empty() => variables.get(&path.root).cloned(),
        ExprKind::Unary { operator, operand } => {
            let value = eval_expression(hir, field, *operand, variables)?;
            match operator {
                UnaryOperator::Negate => Some(field.negate(&value)),
                UnaryOperator::BooleanNot => {
                    Some(field.canonical(i32::from(field.is_zero(&value)).into()))
                }
                UnaryOperator::Complement => None,
            }
        }
        ExprKind::Binary { operator, left, right } => {
            let left = eval_expression(hir, field, *left, variables)?;
            let right = eval_expression(hir, field, *right, variables)?;
            match operator {
                BinaryOperator::Add => Some(field.add(&left, &right)),
                BinaryOperator::Subtract => Some(field.subtract(&left, &right)),
                BinaryOperator::Multiply => Some(field.multiply(&left, &right)),
                BinaryOperator::Equal => Some(field.canonical(i32::from(left == right).into())),
                BinaryOperator::NotEqual => Some(field.canonical(i32::from(left != right).into())),
                _ => None,
            }
        }
        ExprKind::Ternary { condition, yes, no } => {
            let condition = eval_expression(hir, field, *condition, variables)?;
            let selected = if field.is_zero(&condition) { no } else { yes };
            eval_expression(hir, field, *selected, variables)
        }
        ExprKind::Parallel(operand) => eval_expression(hir, field, *operand, variables),
        ExprKind::Access(_)
        | ExprKind::Call { .. }
        | ExprKind::AnonymousComponent { .. }
        | ExprKind::Array(_)
        | ExprKind::Tuple(_)
        | ExprKind::Opaque(_) => None,
    }
}
