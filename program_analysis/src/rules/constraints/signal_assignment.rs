//! Witness-only writes whose exact output has no generated constraint incidence.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use parser::hir::{AccessPath, DefinitionRef, PortId};
use parser::frontend::{PortDirection, Span};

use crate::hir_cfg::{CfgNode, CfgNodeKind};
use crate::hir_facts::{AccessKey, Incidence};
use crate::interprocedural::{ContextOrigin, SummaryBlocker};
use crate::rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult};
use crate::rules::constraints::{opaque_assignment, witness_only};

pub(super) struct SignalAssignment;

impl Rule for SignalAssignment {
    fn kind(&self) -> RuleKind {
        RuleKind::SignalAssignment
    }

    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
        let mut result = RuleResult::default();
        let mut emitted = BTreeSet::new();
        for id in context.facts().cfg().nodes() {
            let Some(node) = context.facts().cfg().node(*id) else { continue };
            inspect_node(context, node, &mut result, &mut emitted);
        }
        result
    }
}

fn inspect_node(
    context: &RuleContext<'_, '_, '_>,
    node: &CfgNode,
    result: &mut RuleResult,
    emitted: &mut BTreeSet<AccessKey>,
) {
    let Some(origin) = node.origin else { return };
    if opaque_assignment(node) {
        if context.facts().reachable_node(node.id).certified() != Some(&false) {
            result.add_abstention(context.abstention(
                RuleKind::SignalAssignment,
                origin.span,
                AbstentionReason::UnsupportedConstruct,
            ));
        }
        return;
    }
    let CfgNodeKind::Witness { target, .. } = &node.kind else { return };
    let effect =
        context.hir().block(origin.block).and_then(|block| block.effects.get(origin.effect_index));
    if !witness_only(effect) {
        return;
    }
    let reachable = context.facts().reachable_node(node.id);
    match reachable.into_result() {
        Ok(false) => return,
        Ok(true) => {}
        Err(blockers) => {
            let reason = AbstentionReason::LocalFacts(blockers);
            result.add_abstention(context.abstention(
                RuleKind::SignalAssignment,
                origin.span,
                reason,
            ));
            return;
        }
    }
    inspect_output(context, target, origin.span, result, emitted);
}

fn inspect_output(
    context: &RuleContext<'_, '_, '_>,
    path: &AccessPath,
    span: Span,
    result: &mut RuleResult,
    emitted: &mut BTreeSet<AccessKey>,
) {
    let Some(port) = declared_output(context, path) else {
        result.add_abstention(context.abstention(
            RuleKind::SignalAssignment,
            span,
            AbstentionReason::UnsupportedConstruct,
        ));
        return;
    };
    let key = context.facts().exact_access_key(path);
    let key = match key.as_result() {
        Ok(key) => key,
        Err(blockers) => {
            let reason = AbstentionReason::LocalFacts(blockers.clone());
            result.add_abstention(context.abstention(RuleKind::SignalAssignment, span, reason));
            return;
        }
    };
    let Some(indices) = key.local_array_indices() else { return };
    let Some(summary) = context.template_port(port, &indices) else { return };
    let summary = match summary.as_result() {
        Ok(summary) => summary,
        Err(blockers) => {
            let reason = AbstentionReason::Summary(blockers.clone());
            result.add_abstention(context.abstention(RuleKind::SignalAssignment, span, reason));
            return;
        }
    };
    match summary.incidence() {
        Incidence::Zero => report_zero(context, key, span, result, emitted),
        Incidence::Must => {}
        Incidence::May => result.add_abstention(context.abstention(
            RuleKind::SignalAssignment,
            span,
            AbstentionReason::UnsupportedConstruct,
        )),
    }
}

fn declared_output(context: &RuleContext<'_, '_, '_>, path: &AccessPath) -> Option<PortId> {
    let DefinitionRef::Template(id) = context.call_context().definition() else { return None };
    if path.root != path.terminal {
        return None;
    }
    for id in &context.hir().template(id)?.ports {
        let port = context.hir().port(*id)?;
        if port.symbol == path.root && port.direction == Some(PortDirection::Output) {
            return Some(*id);
        }
    }
    None
}

fn report_zero(
    context: &RuleContext<'_, '_, '_>,
    key: &AccessKey,
    span: Span,
    result: &mut RuleResult,
    emitted: &mut BTreeSet<AccessKey>,
) {
    match context.origin() {
        ContextOrigin::Call(_) => {
            let reason =
                AbstentionReason::Summary(BTreeSet::from([SummaryBlocker::ExternalSummary]));
            result.add_abstention(context.abstention(RuleKind::SignalAssignment, span, reason));
        }
        ContextOrigin::SymbolicRoot | ContextOrigin::Main(_) => {
            if emitted.insert(key.clone()) {
                result.add_finding(
                    context.finding(
                        RuleKind::SignalAssignment,
                        concat!(
                            "This witness assignment does not constrain the signal. ",
                            "No generated constraint depends on this exact output path."
                        )
                        .into(),
                        span,
                        "Witness-only assignment to an output with zero constraint incidence"
                            .into(),
                    ),
                );
            }
        }
    }
}
