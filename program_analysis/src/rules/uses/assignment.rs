use abstract_interpretation::graph::FlowGraph;
use parser::hir::{AccessPath, DefinitionRef, SymbolId, SymbolKind};
use parser::frontend::AssignmentOperator;

use crate::hir_cfg::{CfgNode, CfgNodeKind};
use crate::hir_facts::{AssignmentDemand, Incidence};
use crate::rules::{AbstentionReason, RuleContext, RuleKind, RuleResult};
use crate::rules::uses::{summary_abstain, summary_reason, validated};

pub(super) fn side_effect_free(context: &RuleContext<'_, '_, '_>, result: &mut RuleResult) {
    let kind = RuleKind::SideEffectFreeAssignment;
    if !validated(context, kind, result) {
        return;
    }
    for id in context.facts().cfg().nodes() {
        let Some(node) = context.facts().cfg().node(*id) else { continue };
        let target =
            if let CfgNodeKind::Assignment {
                target, operator: AssignmentOperator::Assign, ..
            } = &node.kind
            {
                target
            } else if let CfgNodeKind::DeferredAssignment { target, .. } = &node.kind {
                target
            } else {
                continue;
            };
        let Some(symbol) = context.hir().symbol(target.root) else { continue };
        if symbol.kind != SymbolKind::Variable {
            continue;
        }
        report_removable_assignment(context, node, target, result);
    }
}

fn report_removable_assignment(
    context: &RuleContext<'_, '_, '_>,
    node: &CfgNode,
    target: &AccessPath,
    result: &mut RuleResult,
) {
    if !assignment_reachable(context, node, target, result) {
        return;
    }
    let kind = RuleKind::SideEffectFreeAssignment;
    match context.assignment_demand(node.id, target) {
        Ok(fact) => match fact.into_result() {
            Ok(AssignmentDemand::Unobserved(proof)) => {
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
            Ok(AssignmentDemand::MayBeObserved) => {}
            Err(blockers) => result.add_abstention(context.abstention(
                kind,
                target.span,
                AbstentionReason::LocalFacts(blockers),
            )),
        },
        Err(blocker) => {
            result.add_abstention(context.abstention(kind, target.span, summary_reason(blocker)));
        }
    }
}

fn assignment_reachable(
    context: &RuleContext<'_, '_, '_>,
    node: &CfgNode,
    target: &AccessPath,
    result: &mut RuleResult,
) -> bool {
    let reachable = context.facts().reachable_node(node.id);
    match reachable.into_result() {
        Ok(value) => value,
        Err(blockers) => {
            result.add_abstention(context.abstention(
                RuleKind::SideEffectFreeAssignment,
                target.span,
                AbstentionReason::LocalFacts(blockers),
            ));
            false
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
        if let CfgNodeKind::Assignment { target, operator: AssignmentOperator::Assign, .. }
        | CfgNodeKind::DeferredAssignment {
            target,
            operator: AssignmentOperator::Assign,
            ..
        } = &node.kind
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
    match reachable.into_result() {
        Ok(true) => {}
        Ok(false) => return,
        Err(blockers) => {
            result.add_abstention(context.abstention(
                kind,
                target.span,
                AbstentionReason::LocalFacts(blockers),
            ));
            return;
        }
    }
    let live = context.facts().live_after(node.id, target);
    match live.into_result() {
        Ok(false) => {
            let Some(symbol) = context.hir().symbol(target.root) else { return };
            let message = format!("Assigned value of `{}` is never read", symbol.name);
            result.add_finding(context.finding(kind, message, target.span, "unused value".into()));
        }
        Ok(true) => {}
        Err(blockers) => result.add_abstention(context.abstention(
            kind,
            target.span,
            AbstentionReason::LocalFacts(blockers),
        )),
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
            summary_abstain(
                context,
                RuleKind::UnusedVariableValue,
                target.span,
                &incidence,
                result,
            );
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
