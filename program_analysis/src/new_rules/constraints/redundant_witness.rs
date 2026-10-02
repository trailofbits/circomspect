//! Witness assignments whose equation is already generated on every reachable path.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use parser::hir::AccessPath;

use crate::hir_cfg::{CfgNode, CfgNodeKind};
use crate::hir_facts::{AccessKey, GeneratedEquation};
use crate::new_rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult};
use crate::new_rules::constraints::{abstain, opaque_assignment, witness_only};

pub(super) struct RedundantWitness;

impl Rule for RedundantWitness {
    fn kind(&self) -> RuleKind {
        RuleKind::RedundantWitnessAssignment
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
    let kind = RuleKind::RedundantWitnessAssignment;
    if opaque_assignment(node) {
        if context.facts().reachable_node(node.id).certified() != Some(&false) {
            abstain(context, result, kind, origin.span, AbstentionReason::UnsupportedConstruct);
        }
        return;
    }
    let CfgNodeKind::Witness { target, .. } = &node.kind else { return };
    let effect =
        context.hir().block(origin.block).and_then(|block| block.effects.get(origin.effect_index));
    if !witness_only(effect) {
        return;
    }
    if context.facts().reachable_node(node.id).certified() == Some(&false) {
        return;
    }
    inspect_equation(context, node, target, result, emitted);
}

fn inspect_equation(
    context: &RuleContext<'_, '_, '_>,
    node: &CfgNode,
    target: &AccessPath,
    result: &mut RuleResult,
    emitted: &mut BTreeSet<AccessKey>,
) {
    let Some(origin) = node.origin else { return };
    let kind = RuleKind::RedundantWitnessAssignment;
    let equation = context.template_generated_equation(node.id);
    let Some(equation) = equation.certified() else {
        let reason = AbstentionReason::Summary(equation.unavailable().cloned().unwrap_or_default());
        abstain(context, result, kind, origin.span, reason);
        return;
    };
    let Some(equation) = equation else { return };
    let key = context.facts().exact_access_key(target);
    let Some(key) = key.certified() else {
        let reason = AbstentionReason::LocalFacts(key.unavailable().cloned().unwrap_or_default());
        abstain(context, result, kind, origin.span, reason);
        return;
    };
    if emitted.insert(key.clone()) {
        report_equation(context, equation, result);
    }
}

fn report_equation(
    context: &RuleContext<'_, '_, '_>,
    equation: &GeneratedEquation,
    result: &mut RuleResult,
) {
    let mut finding = context.finding(
        RuleKind::RedundantWitnessAssignment,
        concat!(
            "The normalized equation of this witness assignment is already generated ",
            "on every reachable path."
        )
        .into(),
        equation.witness_origin().span,
        "Witness assignment matches an existing generated equation".into(),
    );
    for origin in equation.constraint_origins() {
        finding = finding.with_secondary(origin.span, "Equivalent generated equation".into());
    }
    result.add_finding(finding);
}
