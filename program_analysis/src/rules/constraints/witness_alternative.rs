//! Witness-only writes with a checked alternate satisfying value.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use parser::frontend::{BinaryOperator, UnaryOperator};
use parser::hir::{DefinitionRef, ExprId, ExprKind, HirProject, Knownness};

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::AccessKey;
use crate::rules::constraints::witness_only;
use crate::rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult};

pub(super) struct AlternateWitnessValue;

impl Rule for AlternateWitnessValue {
    fn kind(&self) -> RuleKind {
        RuleKind::AlternateWitnessValue
    }

    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
        let mut result = RuleResult::default();
        if context.main().is_none() {
            return result;
        }
        let DefinitionRef::Template(_) = context.call_context().definition() else {
            return result;
        };
        let mut candidates = Vec::new();
        let mut unsupported = None;
        for id in context.facts().cfg().nodes() {
            let Some(node) = context.facts().cfg().node(*id) else { continue };
            let CfgNodeKind::Witness { value, .. } = &node.kind else { continue };
            let Some(origin) = node.origin else { continue };
            let effect = context
                .hir()
                .block(origin.block)
                .and_then(|block| block.effects.get(origin.effect_index));
            if witness_only(effect) {
                if !witness_expression_supported(context.hir(), *value) {
                    unsupported = Some(origin.span);
                }
                candidates.push((node.id, origin.span));
            }
        }
        if candidates.is_empty() {
            return result;
        }
        if let Some(span) = unsupported {
            result.add_abstention(context.abstention(
                self.kind(),
                span,
                AbstentionReason::UnsupportedConstruct,
            ));
            return result;
        }
        let queries = context.template_generated_equations();
        let mut emitted = BTreeSet::<AccessKey>::new();
        for (id, span) in candidates {
            match queries.witness_alternative(id).as_result() {
                Ok(Some(proof)) if emitted.insert(proof.target.clone()) => {
                    let Some(symbol) = context.hir().symbol(proof.target.root) else { continue };
                    let Some(indices) = proof.target.local_array_indices() else { continue };
                    let name = format_path(&symbol.name, &indices);
                    let witnessed = proof.witnessed.as_bigint();
                    let alternate = proof.alternate.as_bigint();
                    let finding = context.finding(
                        self.kind(),
                        format!(
                            "Witness assignment to `{name}` computes {witnessed}, but \
                             {alternate} also satisfies every generated constraint for the same inputs."
                        ),
                        span,
                        "This witness assignment has an alternate satisfying value.".into(),
                    ).with_secondary(
                        proof.constraint_origin.span,
                        "This quadratic equation admits the alternate value.".into(),
                    );
                    result.add_finding(finding);
                }
                Ok(_) => {}
                Err(blockers) => result.add_abstention(context.abstention(
                    self.kind(),
                    span,
                    AbstentionReason::Summary(blockers.clone()),
                )),
            }
        }
        result
    }
}

fn format_path(name: &str, indices: &[usize]) -> String {
    let mut path = name.to_owned();
    for index in indices {
        path.push('[');
        path.push_str(&index.to_string());
        path.push(']');
    }
    path
}

fn witness_expression_supported(hir: &HirProject, expression: ExprId) -> bool {
    let mut pending = vec![expression];
    let mut visited = BTreeSet::new();
    while let Some(id) = pending.pop() {
        if !visited.insert(id) {
            continue;
        }
        let Some(expression) = hir.expression(id) else { return false };
        match expression.knownness {
            Knownness::Constant | Knownness::ParameterDependent => continue,
            Knownness::Opaque => return false,
            Knownness::WitnessDependent => {}
        }
        let Some(children) = polynomial_children(&expression.kind) else { return false };
        pending.extend(children.into_iter().flatten());
    }
    true
}

fn polynomial_children(kind: &ExprKind) -> Option<[Option<ExprId>; 2]> {
    match kind {
        ExprKind::Number(_) | ExprKind::Access(_) => Some([None, None]),
        ExprKind::Parallel(inner)
        | ExprKind::Unary { operator: UnaryOperator::Negate, operand: inner } => {
            Some([Some(*inner), None])
        }
        ExprKind::Binary { operator, left, right } => match operator {
            BinaryOperator::Add | BinaryOperator::Subtract | BinaryOperator::Multiply => {
                Some([Some(*left), Some(*right)])
            }
            BinaryOperator::BooleanOr
            | BinaryOperator::BooleanAnd
            | BinaryOperator::Equal
            | BinaryOperator::NotEqual
            | BinaryOperator::Less
            | BinaryOperator::Greater
            | BinaryOperator::LessEqual
            | BinaryOperator::GreaterEqual
            | BinaryOperator::BitOr
            | BinaryOperator::BitXor
            | BinaryOperator::BitAnd
            | BinaryOperator::ShiftLeft
            | BinaryOperator::ShiftRight
            | BinaryOperator::Divide
            | BinaryOperator::IntegerDivide
            | BinaryOperator::Modulo
            | BinaryOperator::Power => None,
        },
        ExprKind::Unary {
            operator: UnaryOperator::BooleanNot | UnaryOperator::Complement, ..
        }
        | ExprKind::Call { .. }
        | ExprKind::AnonymousComponent { .. }
        | ExprKind::Array(_)
        | ExprKind::Tuple(_)
        | ExprKind::Ternary { .. }
        | ExprKind::Opaque(_) => None,
    }
}
