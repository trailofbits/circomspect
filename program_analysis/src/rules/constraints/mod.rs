//! Constraint and signal warning family.

mod internal_signal;
mod comparator;
mod redundant_witness;
mod signal_assignment;
mod signal_assert;
mod output_completeness;
mod comparator_precondition;
mod public_input;
mod witness_alternative;

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
    RuleKind::SignalDependentAssert,
    RuleKind::UnassignedOutput,
    RuleKind::ComparatorPrecondition,
    RuleKind::UnusedPublicInput,
    RuleKind::AlternateWitnessValue,
];

/// Constraint rules enter the registry in this family's declared order.
#[must_use]
pub fn rules() -> &'static [&'static dyn Rule] {
    &[
        &SignalAssignment,
        &RedundantWitness,
        &UnconstrainedSignal,
        &crate::rules::constraints::comparator::Comparator,
        &signal_assert::SignalAssert,
        &output_completeness::OutputCompleteness,
        &comparator_precondition::ComparatorPrecondition,
        &public_input::UnusedPublicInput,
        &witness_alternative::AlternateWitnessValue,
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
