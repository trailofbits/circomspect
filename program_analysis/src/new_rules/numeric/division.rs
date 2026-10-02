use std::collections::BTreeSet;

use parser::hir::{AccessPath, Effect, Expr, ExprId, ExprKind, SymbolKind};
use parser::new_frontend::{BinaryOperator, PortDirection, Span};

use crate::hir_facts::Incidence;
use crate::interprocedural::{ContextOrigin, SummaryBlocker};
use crate::new_rules::{AbstentionReason, RuleContext, RuleKind, RuleResult};
use crate::new_rules::numeric::{abstain, contained, definition_span, expressions, reachable};

fn witness_values(context: &RuleContext<'_, '_, '_>) -> (Vec<ExprId>, Vec<Span>) {
    let Some(span) = definition_span(context) else { return (Vec::new(), Vec::new()) };
    let mut values = Vec::new();
    let mut opaque = Vec::new();
    for block in context.hir().blocks() {
        if !contained(block.span, span) {
            continue;
        }
        for effect in &block.effects {
            if let Effect::WitnessAssignment { value, .. } = effect {
                values.push(*value);
            }
            if let Effect::Opaque { span, .. } | Effect::OpaqueAssignment { span, .. } = effect {
                opaque.push(*span);
            }
        }
    }
    (values, opaque)
}

fn is_input(context: &RuleContext<'_, '_, '_>, path: &AccessPath) -> bool {
    if path.root != path.terminal {
        return false;
    }
    if !context.hir().symbol(path.root).is_some_and(|symbol| symbol.kind == SymbolKind::Signal) {
        return false;
    }
    context
        .hir()
        .ports()
        .iter()
        .any(|port| port.symbol == path.root && port.direction == Some(PortDirection::Input))
}

fn inspect_divisor(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    expression: &Expr,
    divisor: parser::hir::ExprId,
) {
    let kind = RuleKind::UnconstrainedDivision;
    let Some(Expr { kind: ExprKind::Access(path), .. }) = context.hir().expression(divisor) else {
        abstain(context, result, kind, expression.span, AbstentionReason::UnsupportedConstruct);
        return;
    };
    if !is_input(context, path) {
        abstain(context, result, kind, expression.span, AbstentionReason::UnsupportedConstruct);
        return;
    }
    let dependencies = context.facts().dependencies(divisor);
    let Some(dependencies) = dependencies.certified() else {
        let reason =
            AbstentionReason::LocalFacts(dependencies.unavailable().cloned().unwrap_or_default());
        abstain(context, result, kind, expression.span, reason);
        return;
    };
    if dependencies.len() != 1 || !dependencies.iter().all(|key| key.exact_alias(key)) {
        abstain(context, result, kind, expression.span, AbstentionReason::UnsupportedConstruct);
        return;
    }
    let incidence = context.facts().incidence(path);
    match incidence.certified() {
        Some(Incidence::Zero) => report_local_zero_incidence(context, result, expression),
        Some(Incidence::May | Incidence::Must) => {}
        None => {
            let reason =
                AbstentionReason::LocalFacts(incidence.unavailable().cloned().unwrap_or_default());
            abstain(context, result, kind, expression.span, reason);
        }
    }
}

fn report_local_zero_incidence(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    expression: &Expr,
) {
    let kind = RuleKind::UnconstrainedDivision;
    match context.origin() {
        ContextOrigin::SymbolicRoot | ContextOrigin::Main(_) => {
            result.add_finding(
                context.finding(
                    kind,
                    "No generated constraint depends on this exact input divisor or excludes zero."
                        .into(),
                    expression.span,
                    "Witness-only division has an unconstrained input divisor".into(),
                ),
            );
        }
        ContextOrigin::Call(_) => {
            let reason =
                AbstentionReason::Summary(BTreeSet::from([SummaryBlocker::ExternalSummary]));
            abstain(context, result, kind, expression.span, reason);
        }
    }
}

pub(super) fn unconstrained_division(context: &RuleContext<'_, '_, '_>) -> RuleResult {
    let mut result = RuleResult::default();
    let (witnesses, opaque) = witness_values(context);
    for span in opaque {
        abstain(
            context,
            &mut result,
            RuleKind::UnconstrainedDivision,
            span,
            AbstentionReason::UnsupportedConstruct,
        );
    }
    for value in &witnesses {
        if let Some(Expr { kind: ExprKind::Opaque(_), span, .. }) = context.hir().expression(*value)
        {
            abstain(
                context,
                &mut result,
                RuleKind::UnconstrainedDivision,
                *span,
                AbstentionReason::UnsupportedConstruct,
            );
        }
    }
    for expression in expressions(context) {
        let ExprKind::Binary { operator, right, .. } = &expression.kind else { continue };
        if *operator != BinaryOperator::Divide && *operator != BinaryOperator::IntegerDivide {
            continue;
        }
        if !witnesses.iter().any(|id| {
            context.hir().expression(*id).is_some_and(|root| contained(expression.span, root.span))
        }) {
            continue;
        }
        if !reachable(context, &mut result, RuleKind::UnconstrainedDivision, expression) {
            continue;
        }
        inspect_divisor(context, &mut result, expression, *right);
    }
    result
}
