//! Witness assignments whose equation is already generated on every reachable path.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;

use crate::hir_cfg::{CfgNode, CfgNodeKind};
use crate::hir_facts::{AccessKey, GeneratedEquation};
use crate::interprocedural::GeneratedEquationQueries;
use crate::new_rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult};
use crate::new_rules::constraints::{opaque_assignment, witness_only};

pub(super) struct RedundantWitness;

impl Rule for RedundantWitness {
    fn kind(&self) -> RuleKind {
        RuleKind::RedundantWitnessAssignment
    }

    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
        let mut result = RuleResult::default();
        let mut candidates = Vec::new();
        for id in context.facts().cfg().nodes() {
            let Some(node) = context.facts().cfg().node(*id) else { continue };
            if is_candidate(context, node, &mut result) {
                candidates.push(node);
            }
        }
        if candidates.is_empty() {
            return result;
        }
        let equations = context.template_generated_equations();
        let mut emitted = BTreeSet::new();
        for node in candidates {
            inspect_equation(context, node, &equations, &mut result, &mut emitted);
        }
        result
    }
}

fn is_candidate(
    context: &RuleContext<'_, '_, '_>,
    node: &CfgNode,
    result: &mut RuleResult,
) -> bool {
    let Some(origin) = node.origin else { return false };
    let kind = RuleKind::RedundantWitnessAssignment;
    if opaque_assignment(node) {
        if context.facts().reachable_node(node.id).certified() != Some(&false) {
            result.add_abstention(context.abstention(
                kind,
                origin.span,
                AbstentionReason::UnsupportedConstruct,
            ));
        }
        return false;
    }
    let CfgNodeKind::Witness { .. } = &node.kind else { return false };
    let effect =
        context.hir().block(origin.block).and_then(|block| block.effects.get(origin.effect_index));
    witness_only(effect) && context.facts().reachable_node(node.id).certified() != Some(&false)
}

fn inspect_equation(
    context: &RuleContext<'_, '_, '_>,
    node: &CfgNode,
    equations: &GeneratedEquationQueries<'_, '_>,
    result: &mut RuleResult,
    emitted: &mut BTreeSet<AccessKey>,
) {
    let Some(origin) = node.origin else { return };
    let kind = RuleKind::RedundantWitnessAssignment;
    let equation = equations.for_witness(node.id);
    let Some(equation) = equation.certified() else {
        let reason = AbstentionReason::Summary(equation.unavailable().cloned().unwrap_or_default());
        result.add_abstention(context.abstention(kind, origin.span, reason));
        return;
    };
    let Some(equation) = equation else { return };
    let CfgNodeKind::Witness { target, .. } = &node.kind else { return };
    let key = context.facts().exact_access_key(target);
    let key = match key.as_result() {
        Ok(key) => key,
        Err(blockers) => {
            let reason = AbstentionReason::LocalFacts(blockers.clone());
            result.add_abstention(context.abstention(kind, origin.span, reason));
            return;
        }
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
