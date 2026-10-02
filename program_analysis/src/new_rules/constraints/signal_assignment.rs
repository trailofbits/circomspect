//! Witness-only writes whose exact output has no generated constraint incidence.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use num_traits::ToPrimitive;
use parser::hir::{AccessPath, DefinitionRef, Effect, PortId};
use parser::new_frontend::{AssignmentOperator, PortDirection, Span};

use crate::hir_cfg::{CfgNode, CfgNodeKind};
use crate::hir_facts::{AccessKey, AccessKeyStep, Incidence, IndexKey};
use crate::interprocedural::{ContextOrigin, SummaryBlocker};
use crate::new_rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult};
use crate::new_rules::constraints::abstain;

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
            abstain(
                context,
                result,
                RuleKind::SignalAssignment,
                origin.span,
                AbstentionReason::UnsupportedConstruct,
            );
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
    match reachable.certified() {
        Some(false) => return,
        Some(true) => {}
        None => {
            let reason =
                AbstentionReason::LocalFacts(reachable.unavailable().cloned().unwrap_or_default());
            abstain(context, result, RuleKind::SignalAssignment, origin.span, reason);
            return;
        }
    }
    inspect_output(context, target, origin.span, result, emitted);
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

fn inspect_output(
    context: &RuleContext<'_, '_, '_>,
    path: &AccessPath,
    span: Span,
    result: &mut RuleResult,
    emitted: &mut BTreeSet<AccessKey>,
) {
    let Some(port) = declared_output(context, path) else {
        abstain(
            context,
            result,
            RuleKind::SignalAssignment,
            span,
            AbstentionReason::UnsupportedConstruct,
        );
        return;
    };
    let key = context.facts().exact_access_key(path);
    let Some(key) = key.certified() else {
        let reason = AbstentionReason::LocalFacts(key.unavailable().cloned().unwrap_or_default());
        abstain(context, result, RuleKind::SignalAssignment, span, reason);
        return;
    };
    let Some(indices) = port_indices(key) else { return };
    let Some(summary) = context.template_port(port, &indices) else { return };
    let Some(summary) = summary.certified() else {
        let reason = AbstentionReason::Summary(summary.unavailable().cloned().unwrap_or_default());
        abstain(context, result, RuleKind::SignalAssignment, span, reason);
        return;
    };
    match summary.incidence() {
        Incidence::Zero => report_zero(context, key, span, result, emitted),
        Incidence::Must => {}
        Incidence::May => abstain(
            context,
            result,
            RuleKind::SignalAssignment,
            span,
            AbstentionReason::UnsupportedConstruct,
        ),
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

fn port_indices(key: &AccessKey) -> Option<Vec<usize>> {
    let mut indices = Vec::new();
    for step in &key.steps {
        let AccessKeyStep::Index(IndexKey::Exact(value)) = step else { return None };
        indices.push(value.as_bigint().to_usize()?);
    }
    Some(indices)
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
            abstain(context, result, RuleKind::SignalAssignment, span, reason);
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
