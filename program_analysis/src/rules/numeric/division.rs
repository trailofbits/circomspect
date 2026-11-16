use parser::hir::{AccessPath, DefinitionRef, Effect, Expr, ExprId, ExprKind, PortId, SymbolKind};
use parser::frontend::{BinaryOperator, PortDirection, Span};

use crate::hir_facts::Incidence;
use crate::rules::{AbstentionReason, RuleContext, RuleKind, RuleResult};
use crate::rules::numeric::{contained, definition_span, expressions, reachable};

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

fn declared_input(context: &RuleContext<'_, '_, '_>, path: &AccessPath) -> Option<PortId> {
    let DefinitionRef::Template(id) = context.call_context().definition() else { return None };
    if path.root != path.terminal {
        return None;
    }
    if !context.hir().symbol(path.root).is_some_and(|symbol| symbol.kind == SymbolKind::Signal) {
        return None;
    }
    for id in &context.hir().template(id)?.ports {
        let port = context.hir().port(*id)?;
        if port.symbol == path.root && port.direction == Some(PortDirection::Input) {
            return Some(*id);
        }
    }
    None
}

fn inspect_divisor(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    expression: &Expr,
    divisor: parser::hir::ExprId,
) {
    let kind = RuleKind::UnconstrainedDivision;
    let Some(Expr { kind: ExprKind::Access(path), .. }) = context.hir().expression(divisor) else {
        result.add_abstention(context.abstention(
            kind,
            expression.span,
            AbstentionReason::UnsupportedConstruct,
        ));
        return;
    };
    let Some(port) = declared_input(context, path) else {
        result.add_abstention(context.abstention(
            kind,
            expression.span,
            AbstentionReason::UnsupportedConstruct,
        ));
        return;
    };
    let key = context.facts().exact_access_key(path);
    let key = match key.as_result() {
        Ok(key) => key,
        Err(blockers) => {
            let reason = AbstentionReason::LocalFacts(blockers.clone());
            result.add_abstention(context.abstention(kind, expression.span, reason));
            return;
        }
    };
    let Some(indices) = key.local_array_indices() else {
        result.add_abstention(context.abstention(
            kind,
            expression.span,
            AbstentionReason::UnsupportedConstruct,
        ));
        return;
    };
    let Some(summary) = context.template_port(port, &indices) else { return };
    let summary = match summary.as_result() {
        Ok(summary) => summary,
        Err(blockers) => {
            let reason = AbstentionReason::Summary(blockers.clone());
            result.add_abstention(context.abstention(kind, expression.span, reason));
            return;
        }
    };
    match summary.incidence() {
        Incidence::Zero => report_local_zero_incidence(context, result, expression),
        Incidence::May | Incidence::Must => {}
    }
}

fn report_local_zero_incidence(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    expression: &Expr,
) {
    let kind = RuleKind::UnconstrainedDivision;
    result.add_finding(context.finding(
        kind,
        "No generated constraint depends on this exact input divisor or excludes zero.".into(),
        expression.span,
        "This divisor can be zero without violating a constraint.".into(),
    ));
}

pub(super) fn unconstrained_division(context: &RuleContext<'_, '_, '_>) -> RuleResult {
    let mut result = RuleResult::default();
    let (witnesses, opaque) = witness_values(context);
    for span in opaque {
        result.add_abstention(context.abstention(
            RuleKind::UnconstrainedDivision,
            span,
            AbstentionReason::UnsupportedConstruct,
        ));
    }
    for value in &witnesses {
        if let Some(Expr { kind: ExprKind::Opaque(_), span, .. }) = context.hir().expression(*value)
        {
            result.add_abstention(context.abstention(
                RuleKind::UnconstrainedDivision,
                *span,
                AbstentionReason::UnsupportedConstruct,
            ));
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
