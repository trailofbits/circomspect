//! Source operator descriptions, without a claim that a deferred assignment is valid.

use parser::hir::{AccessPath, Effect, ExprId, IncompleteReason};
use parser::frontend::AssignmentOperator;

pub(crate) enum SourceSignalAssignment<'a> {
    Generated { target: &'a AccessPath, value: ExprId },
    Witness { target: &'a AccessPath, value: ExprId },
}

/// Describe original assignment provenance; consumers must check the solved CFG.
///
/// A deferred source keeps its operator, but this description does not prove
/// scalar shape, execution readiness, or the presence of a generated constraint.
pub(crate) trait DescribeSignalAssignment {
    fn signal_assignment(&self) -> Option<SourceSignalAssignment<'_>>;
}

impl DescribeSignalAssignment for Effect {
    fn signal_assignment(&self) -> Option<SourceSignalAssignment<'_>> {
        match self {
            Self::ConstraintAssignment { target, value, .. } => {
                Some(SourceSignalAssignment::Generated { target, value: *value })
            }
            Self::WitnessAssignment { target, value, .. } => {
                Some(SourceSignalAssignment::Witness { target, value: *value })
            }
            Self::OpaqueAssignment {
                target,
                value,
                operator,
                reason: IncompleteReason::UnknownType,
                ..
            } => match operator {
                AssignmentOperator::Constraint | AssignmentOperator::ReverseConstraint => {
                    Some(SourceSignalAssignment::Generated { target, value: *value })
                }
                AssignmentOperator::Witness | AssignmentOperator::ReverseWitness => {
                    Some(SourceSignalAssignment::Witness { target, value: *value })
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
                | AssignmentOperator::BitXor => None,
            },
            Self::Discard { .. }
            | Self::Declaration { .. }
            | Self::VariableAssignment { .. }
            | Self::DeferredVariableAssignment { .. }
            | Self::ComponentInstantiation { .. }
            | Self::OpaqueAssignment { .. }
            | Self::EqualityConstraint { .. }
            | Self::OpaqueEquality { .. }
            | Self::Update { .. }
            | Self::If { .. }
            | Self::While { .. }
            | Self::For { .. }
            | Self::Return { .. }
            | Self::Assert { .. }
            | Self::DeferredAssert { .. }
            | Self::Log { .. }
            | Self::AnonymousComponent { .. }
            | Self::Block(_)
            | Self::Opaque { .. } => None,
        }
    }
}
