use abstract_interpretation::graph::FlowGraph;
use parser::hir::{AccessPath, DefinitionRef, SymbolId, SymbolKind};
use parser::new_frontend::AssignmentOperator;

use crate::hir_cfg::{CfgNode, CfgNodeKind};
use crate::hir_facts::{AssignmentDemand, Incidence};
use crate::new_rules::{AbstentionReason, RuleContext, RuleKind, RuleResult};
use crate::new_rules::uses::{abstain, local_abstain, summary_abstain, summary_reason, validated};

pub(super) fn side_effect_free(context: &RuleContext<'_, '_, '_>, result: &mut RuleResult) {
    let kind = RuleKind::SideEffectFreeAssignment;
    if !validated(context, kind, result) {
        return;
    }
    for id in context.facts().cfg().nodes() {
        let Some(node) = context.facts().cfg().node(*id) else { continue };
        if let CfgNodeKind::DeferredAssignment { target, .. } = &node.kind {
            abstain_deferred_assignment(context, target, result);
            continue;
        }
        let CfgNodeKind::Assignment { target, operator: AssignmentOperator::Assign, .. } =
            &node.kind
        else {
            continue;
        };
        let Some(symbol) = context.hir().symbol(target.root) else { continue };
        if symbol.kind != SymbolKind::Variable {
            continue;
        }
        report_removable_assignment(context, node, target, result);
    }
}

fn abstain_deferred_assignment(
    context: &RuleContext<'_, '_, '_>,
    target: &AccessPath,
    result: &mut RuleResult,
) {
    let Some(symbol) = context.hir().symbol(target.root) else { return };
    if symbol.kind == SymbolKind::Variable {
        abstain(
            result,
            context,
            RuleKind::SideEffectFreeAssignment,
            target.span,
            AbstentionReason::UnsupportedConstruct,
        );
    }
}

fn report_removable_assignment(
    context: &RuleContext<'_, '_, '_>,
    node: &CfgNode,
    target: &AccessPath,
    result: &mut RuleResult,
) {
    let kind = RuleKind::SideEffectFreeAssignment;
    match context.assignment_demand(node.id, target) {
        Ok(fact) => match fact.certified() {
            Some(AssignmentDemand::Unobserved(proof)) => {
                let Some(symbol) = context.hir().symbol(target.root) else { return };
                let message = format!(
                    "Assignment to `{}` has no observable effect; its value is unused",
                    symbol.name
                );
                result.add_finding(context.finding(
                    kind,
                    message,
                    proof.span(),
                    "unused value".into(),
                ));
            }
            Some(AssignmentDemand::MayBeObserved) => {}
            None => local_abstain(context, kind, target.span, &fact, result),
        },
        Err(blocker) => {
            abstain(result, context, kind, target.span, summary_reason(blocker));
        }
    }
}

pub(super) fn unused_values(context: &RuleContext<'_, '_, '_>, result: &mut RuleResult) {
    let kind = RuleKind::UnusedVariableValue;
    if !validated(context, kind, result) {
        return;
    }
    for id in context.facts().cfg().nodes() {
        let Some(node) = context.facts().cfg().node(*id) else { continue };
        if let CfgNodeKind::Assignment { target, operator: AssignmentOperator::Assign, .. } =
            &node.kind
        {
            if context
                .hir()
                .symbol(target.root)
                .is_some_and(|symbol| symbol.kind == SymbolKind::Variable)
            {
                report_unused_value(context, node, target, result);
            }
        }
        if let CfgNodeKind::Witness { target, .. } = &node.kind {
            unused_internal_signal(context, node, target, result);
        }
    }
}

fn report_unused_value(
    context: &RuleContext<'_, '_, '_>,
    node: &CfgNode,
    target: &AccessPath,
    result: &mut RuleResult,
) {
    let kind = RuleKind::UnusedVariableValue;
    let reachable = context.facts().reachable_node(node.id);
    if reachable.certified() != Some(&true) {
        local_abstain(context, kind, target.span, &reachable, result);
        return;
    }
    let live = context.facts().live_after(node.id, target);
    match live.certified() {
        Some(false) => {
            let Some(symbol) = context.hir().symbol(target.root) else { return };
            let message = format!("Assigned value of `{}` is never read", symbol.name);
            result.add_finding(context.finding(kind, message, target.span, "unused value".into()));
        }
        Some(true) => {}
        None => local_abstain(context, kind, target.span, &live, result),
    }
}

fn unused_internal_signal(
    context: &RuleContext<'_, '_, '_>,
    node: &CfgNode,
    target: &AccessPath,
    result: &mut RuleResult,
) {
    let Some(symbol) = context.hir().symbol(target.root) else { return };
    if symbol.kind != SymbolKind::Signal || exported_port(context, target.root) {
        return;
    }
    let incidence = context.template_internal_signal_incidence(target);
    match incidence.certified() {
        Some(Incidence::Zero) => report_unused_value(context, node, target, result),
        Some(Incidence::May | Incidence::Must) => {}
        None => {
            summary_abstain(context, RuleKind::UnusedVariableValue, target.span, &incidence, result)
        }
    }
}

fn exported_port(context: &RuleContext<'_, '_, '_>, symbol: SymbolId) -> bool {
    let DefinitionRef::Template(id) = context.call_context().definition() else { return false };
    let Some(template) = context.hir().template(id) else { return true };
    for port in &template.ports {
        let Some(port) = context.hir().port(*port) else { return true };
        if port.symbol == symbol {
            return true;
        }
    }
    false
}
