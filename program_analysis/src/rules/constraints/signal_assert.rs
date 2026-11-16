//! Assertions depending on witness values are checks in witness code, not R1CS constraints.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use parser::frontend::BinaryOperator;
use parser::hir::{ExprId, ExprKind, Knownness};

use crate::hir_cfg::{CfgNodeKind, Constraint};
use crate::hir_facts::VisitAccesses;
use crate::rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult};

pub(super) struct SignalAssert;

impl Rule for SignalAssert {
    fn kind(&self) -> RuleKind {
        RuleKind::SignalDependentAssert
    }

    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
        let mut result = RuleResult::default();
        if let Err(blocker) = context.validated_definition() {
            if let Ok(header) = context.validated_header() {
                result.add_abstention(context.abstention(
                    self.kind(),
                    header.name_span(),
                    AbstentionReason::Summary(BTreeSet::from([blocker])),
                ));
            }
            return result;
        }
        for id in context.facts().cfg().nodes() {
            abstract_interpretation::timeout::check();
            let Some(node) = context.facts().cfg().node(*id) else { continue };
            let (CfgNodeKind::Assert { condition } | CfgNodeKind::DeferredAssert { condition }) =
                node.kind
            else {
                continue;
            };
            let Some(origin) = node.origin else { continue };
            let Some(expression) = context.hir().expression(condition) else { continue };
            match context.facts().reachable_node(node.id).into_result() {
                Ok(true) => {}
                Ok(false) => continue,
                Err(blockers) => {
                    result.add_abstention(context.abstention(
                        self.kind(),
                        origin.span,
                        AbstentionReason::LocalFacts(blockers),
                    ));
                    continue;
                }
            }
            match expression.knownness {
                Knownness::WitnessDependent => {
                    if equivalent_constraint(context, condition) {
                        continue;
                    }
                    let mut names = Vec::new();
                    condition.visit_accesses(context.hir(), &mut |path| {
                        if let Some(symbol) = context.hir().symbol(path.root) {
                            if !names.contains(&symbol.name) {
                                names.push(symbol.name.clone());
                            }
                        }
                    });
                    let detail = if names.is_empty() {
                        "a witness-dependent expression".to_owned()
                    } else {
                        format!("witness-dependent value(s): {}", names.join(", "))
                    };
                    result.add_finding(context.finding(
                        self.kind(),
                        format!(
                            "This assertion checks {detail} only during witness generation; \
                             it adds no constraint to the proof system."
                        ),
                        origin.span,
                        "This assertion does not constrain the proof.".into(),
                    ));
                }
                Knownness::Opaque => result.add_abstention(context.abstention(
                    self.kind(),
                    origin.span,
                    AbstentionReason::UnsupportedConstruct,
                )),
                Knownness::Constant | Knownness::ParameterDependent => {}
            }
        }
        result
    }
}

fn equivalent_constraint(context: &RuleContext<'_, '_, '_>, condition: ExprId) -> bool {
    let Some(expression) = context.hir().expression(condition) else { return false };
    let ExprKind::Binary { operator: BinaryOperator::Equal, left, right } = expression.kind else {
        return false;
    };
    for id in context.facts().cfg().nodes() {
        let Some(node) = context.facts().cfg().node(*id) else { continue };
        if context.facts().must_execute(node.id).certified() != Some(&true) {
            continue;
        }
        match &node.kind {
            CfgNodeKind::Constraint(Constraint::Equality { left: a, right: b }) => {
                if same_pair(context, (left, right), (*a, *b)) {
                    return true;
                }
            }
            CfgNodeKind::Constraint(Constraint::Assignment { target, value })
                if (access_matches(context, left, target)
                    && same_expression(context, right, *value))
                    || (access_matches(context, right, target)
                        && same_expression(context, left, *value)) =>
            {
                return true;
            }
            _ => {}
        }
    }
    false
}

fn same_pair(
    context: &RuleContext<'_, '_, '_>,
    first: (ExprId, ExprId),
    second: (ExprId, ExprId),
) -> bool {
    same_expression(context, first.0, second.0) && same_expression(context, first.1, second.1)
        || same_expression(context, first.0, second.1)
            && same_expression(context, first.1, second.0)
}

fn access_matches(
    context: &RuleContext<'_, '_, '_>,
    expression: ExprId,
    target: &parser::hir::AccessPath,
) -> bool {
    let Some(expression) = context.hir().expression(expression) else { return false };
    let ExprKind::Access(path) = &expression.kind else { return false };
    same_access(context, path, target)
}

fn same_access(
    context: &RuleContext<'_, '_, '_>,
    left: &parser::hir::AccessPath,
    right: &parser::hir::AccessPath,
) -> bool {
    let left = context.facts().exact_access_key(left);
    let right = context.facts().exact_access_key(right);
    matches!((left.certified(), right.certified()), (Some(left), Some(right)) if left == right)
}

fn same_expression(context: &RuleContext<'_, '_, '_>, left: ExprId, right: ExprId) -> bool {
    let Some(left) = context.hir().expression(left) else { return false };
    let Some(right) = context.hir().expression(right) else { return false };
    match (&left.kind, &right.kind) {
        (ExprKind::Number(left), ExprKind::Number(right)) => left == right,
        (ExprKind::Access(left), ExprKind::Access(right)) => same_access(context, left, right),
        (
            ExprKind::Binary { operator: a, left: al, right: ar },
            ExprKind::Binary { operator: b, left: bl, right: br },
        ) => a == b && same_expression(context, *al, *bl) && same_expression(context, *ar, *br),
        _ => false,
    }
}
