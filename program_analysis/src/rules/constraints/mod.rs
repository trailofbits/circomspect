//! Constraint and signal warning family.

mod internal_signal;
mod comparator;
mod redundant_witness;
mod signal_assignment;

use parser::hir::Effect;
use parser::frontend::AssignmentOperator;

use crate::hir_cfg::{CfgNode, CfgNodeKind};
use crate::rules::{Rule, RuleKind};
use crate::rules::constraints::internal_signal::UnconstrainedSignal;
use crate::rules::constraints::redundant_witness::RedundantWitness;
use crate::rules::constraints::signal_assignment::SignalAssignment;

pub const KINDS: &[RuleKind] = &[
    RuleKind::SignalAssignment,
    RuleKind::RedundantWitnessAssignment,
    RuleKind::UnconstrainedSignal,
    RuleKind::UnconstrainedLessThan,
];

/// Constraint rules enter the registry in this family's declared order.
#[must_use]
pub fn rules() -> &'static [&'static dyn Rule] {
    &[
        &SignalAssignment,
        &RedundantWitness,
        &UnconstrainedSignal,
        &crate::rules::constraints::comparator::Comparator,
    ]
}

fn witness_only(effect: Option<&Effect>) -> bool {
    if let Some(Effect::WitnessAssignment { .. }) = effect {
        return true;
    }
    let Some(Effect::OpaqueAssignment { operator, .. }) = effect else { return false };
    *operator == AssignmentOperator::Witness || *operator == AssignmentOperator::ReverseWitness
}

fn opaque_assignment(node: &CfgNode) -> bool {
    if let CfgNodeKind::Opaque(_) = &node.kind {
        return true;
    }
    let CfgNodeKind::OpaqueAssignment { operator, .. } = &node.kind else { return false };
    *operator == AssignmentOperator::Witness || *operator == AssignmentOperator::ReverseWitness
}
