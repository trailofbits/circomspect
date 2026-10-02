use abstract_interpretation::graph::FlowGraph;
use parser::hir::{AccessPath, DefinitionRef, ExprId, ExprKind, SymbolId, SymbolKind};
use parser::new_frontend::AssignmentOperator;

use crate::hir_cfg::{CfgNode, CfgNodeKind};
use crate::hir_facts::Incidence;
use crate::new_rules::{AbstentionReason, RuleContext, RuleKind, RuleResult};
use crate::new_rules::uses::{abstain, local_abstain, validated};

#[derive(Clone, Copy)]
enum DeadAssignmentClaim {
    SideEffectFree,
    UnusedValue,
}

impl DeadAssignmentClaim {
    fn kind(self) -> RuleKind {
        match self {
            Self::SideEffectFree => RuleKind::SideEffectFreeAssignment,
            Self::UnusedValue => RuleKind::UnusedVariableValue,
        }
    }

    fn message(self, name: &str) -> String {
        match self {
            Self::SideEffectFree => {
                format!("Assignment to `{name}` has no observable effect; its value is unused")
            }
            Self::UnusedValue => format!("Assigned value of `{name}` is never read"),
        }
    }
}

pub(super) fn side_effect_free(context: &RuleContext<'_, '_, '_>, result: &mut RuleResult) {
    let kind = RuleKind::SideEffectFreeAssignment;
    if !validated(context, kind, result) {
        return;
    }
    for id in context.facts().cfg().nodes() {
        let Some(node) = context.facts().cfg().node(*id) else { continue };
        let CfgNodeKind::Assignment { target, value, operator } = &node.kind else { continue };
        if *operator != AssignmentOperator::Assign
            || !pure_local_assignment(context, target, *value)
        {
            continue;
        }
        report_dead_assignment(context, DeadAssignmentClaim::SideEffectFree, node, target, result);
    }
}

fn pure_local_assignment(
    context: &RuleContext<'_, '_, '_>,
    target: &AccessPath,
    value: ExprId,
) -> bool {
    let Some(symbol) = context.hir().symbol(target.root) else { return false };
    if symbol.kind != SymbolKind::Variable || symbol.rank != 0 || !target.steps.is_empty() {
        return false;
    }
    let Some(expression) = context.hir().expression(value) else { return false };
    match &expression.kind {
        ExprKind::Number(_) => true,
        ExprKind::Access(path) => {
            let Some(read) = context.hir().symbol(path.root) else { return false };
            read.rank == 0
                && path.steps.is_empty()
                && !path.component_input
                && !path.component_output
        }
        ExprKind::Unary { .. }
        | ExprKind::Binary { .. }
        | ExprKind::Array(_)
        | ExprKind::Tuple(_)
        | ExprKind::Call { .. }
        | ExprKind::AnonymousComponent { .. }
        | ExprKind::Ternary { .. }
        | ExprKind::Parallel(_)
        | ExprKind::Opaque(_) => false,
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
                report_dead_assignment(
                    context,
                    DeadAssignmentClaim::UnusedValue,
                    node,
                    target,
                    result,
                );
            }
        }
        if let CfgNodeKind::Witness { target, .. } = &node.kind {
            unused_internal_signal(context, node, target, result);
        }
    }
}

fn report_dead_assignment(
    context: &RuleContext<'_, '_, '_>,
    claim: DeadAssignmentClaim,
    node: &CfgNode,
    target: &AccessPath,
    result: &mut RuleResult,
) {
    let kind = claim.kind();
    let reachable = context.facts().reachable_node(node.id);
    if reachable.certified() != Some(&true) {
        local_abstain(context, kind, target.span, &reachable, result);
        return;
    }
    let live = context.facts().live_after(node.id, target);
    match live.certified() {
        Some(false) => {
            let name = &context.hir().symbol(target.root).unwrap().name;
            let message = claim.message(name);
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
    let incidence = context.facts().incidence(target);
    match incidence.certified() {
        Some(Incidence::Zero) => {
            report_dead_assignment(context, DeadAssignmentClaim::UnusedValue, node, target, result)
        }
        Some(Incidence::May | Incidence::Must) => {}
        None => {
            if let Some(blockers) = incidence.unavailable() {
                abstain(
                    result,
                    context,
                    RuleKind::UnusedVariableValue,
                    target.span,
                    AbstentionReason::LocalFacts(blockers.clone()),
                );
            }
        }
    }
}

fn exported_port(context: &RuleContext<'_, '_, '_>, symbol: SymbolId) -> bool {
    let DefinitionRef::Template(id) = context.call_context().definition() else { return false };
    let Some(template) = context.hir().template(id) else { return false };
    template
        .ports
        .iter()
        .any(|port| context.hir().port(*port).is_some_and(|port| port.symbol == symbol))
}
