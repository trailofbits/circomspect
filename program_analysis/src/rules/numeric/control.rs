use std::collections::BTreeSet;

use num_traits::Zero;
use parser::hir::{Effect, ExprId, ExprKind};

use crate::rules::{RuleContext, RuleKind, RuleResult};

use super::{contained, definition_span, exact_value, expressions, reachable};

fn condition_ids(context: &RuleContext<'_, '_, '_>) -> BTreeSet<ExprId> {
    let Some(span) = definition_span(context) else { return BTreeSet::new() };
    let mut ids = BTreeSet::new();
    for block in context.hir().blocks() {
        if !contained(block.span, span) {
            continue;
        }
        for effect in &block.effects {
            if let Effect::If { condition, .. }
            | Effect::While { condition, .. }
            | Effect::For { condition, .. } = effect
            {
                ids.insert(*condition);
            }
        }
    }
    for expression in expressions(context) {
        if let ExprKind::Ternary { condition, .. } = &expression.kind {
            ids.insert(*condition);
        }
    }
    ids
}

pub(super) fn constant_conditional(context: &RuleContext<'_, '_, '_>) -> RuleResult {
    let mut result = RuleResult::default();
    for id in condition_ids(context) {
        let Some(expression) = context.hir().expression(id) else { continue };
        if !reachable(context, &mut result, RuleKind::ConstantConditional, expression) {
            continue;
        }
        let value = match exact_value(context, id) {
            Ok(value) => value,
            Err(reason) => {
                result.add_abstention(context.abstention(
                    RuleKind::ConstantConditional,
                    expression.span,
                    reason,
                ));
                continue;
            }
        };
        let boolean = !value.as_bigint().is_zero();
        result.add_finding(context.finding(
            RuleKind::ConstantConditional,
            format!("This condition is always {boolean} in the reported call context."),
            expression.span,
            format!("This condition is always {boolean}."),
        ));
    }
    result
}
