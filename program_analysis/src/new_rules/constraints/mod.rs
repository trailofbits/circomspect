//! Constraint and signal warning family.

mod signal_assignment;

use parser::new_frontend::Span;

use crate::new_rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult, ScopedAbstention};
use crate::new_rules::constraints::signal_assignment::SignalAssignment;

pub const KINDS: &[RuleKind] = &[
    RuleKind::SignalAssignment,
    RuleKind::RedundantWitnessAssignment,
    RuleKind::UnconstrainedSignal,
    RuleKind::UnconstrainedLessThan,
];

/// Constraint rules enter the registry in this family's declared order.
pub fn rules() -> &'static [&'static dyn Rule] {
    &[&SignalAssignment]
}

fn abstain(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    kind: RuleKind,
    span: Span,
    reason: AbstentionReason,
) {
    result.add_abstention(ScopedAbstention {
        kind,
        context: context.call_context().clone(),
        span,
        reason,
    });
}
