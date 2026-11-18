//! Checked zero models for witness division by an exact input signal.

use abstract_interpretation::graph::{FlowGraph, NodeId};
use parser::frontend::{BinaryOperator, Span};
use parser::hir::{AccessPath, ExprId, ExprKind};

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::{DescribeSignalAssignment, SourceSignalAssignment};
use crate::interprocedural::ContextOrigin;
use crate::rules::numeric::division::declared_input;
use crate::rules::{AbstentionReason, RuleContext, RuleKind, RuleResult};

struct Candidate {
    witness: NodeId,
    span: Span,
    divisor: AccessPath,
}

pub(super) fn feasible_zero_divisor(context: &RuleContext<'_, '_, '_>) -> RuleResult {
    let mut result = RuleResult::default();
    if context.origin() == ContextOrigin::SymbolicRoot {
        return result;
    }
    let candidates = candidates(context, &mut result);
    if candidates.is_empty() {
        return result;
    }
    let queries = context.template_generated_equations();
    for candidate in candidates {
        let Candidate { witness, span, divisor } = candidate;
        match queries.feasible_zero_divisor(witness, &divisor).as_result() {
            Ok(Some(proof)) => {
                let Some(symbol) = context.hir().symbol(proof.divisor.root) else { continue };
                let message = format!(
                    "A model with `{}` = 0 satisfies all {} generated constraints and reaches \
                     this witness division.",
                    symbol.name, proof.constraint_count,
                );
                result.add_finding(context.finding(
                    RuleKind::FeasibleZeroDivisor,
                    message,
                    span,
                    "Witness generation can divide by zero for this accepted constraint assignment."
                        .into(),
                ));
            }
            Ok(None) => {}
            Err(blockers) => result.add_abstention(context.abstention(
                RuleKind::FeasibleZeroDivisor,
                span,
                AbstentionReason::Summary(blockers.clone()),
            )),
        }
    }
    result
}

fn candidates(context: &RuleContext<'_, '_, '_>, result: &mut RuleResult) -> Vec<Candidate> {
    let mut found = Vec::new();
    for id in context.facts().cfg().nodes() {
        match candidate(context, *id) {
            Ok(Some(candidate)) => found.push(candidate),
            Ok(None) => {}
            Err(span) => result.add_abstention(context.abstention(
                RuleKind::FeasibleZeroDivisor,
                span,
                AbstentionReason::UnsupportedConstruct,
            )),
        }
    }
    found
}

fn candidate(
    context: &RuleContext<'_, '_, '_>,
    witness: NodeId,
) -> Result<Option<Candidate>, Span> {
    let Some(value) = source_witness(context, witness) else { return Ok(None) };
    let Some(expression) = context.hir().expression(value) else { return Ok(None) };
    let ExprKind::Binary { operator, right, .. } = &expression.kind else { return Ok(None) };
    if *operator != BinaryOperator::Divide && *operator != BinaryOperator::IntegerDivide {
        return Ok(None);
    }
    let Some(denominator) = context.hir().expression(*right) else { return Ok(None) };
    let ExprKind::Access(path) = &denominator.kind else { return Err(expression.span) };
    if !path.steps.is_empty() || declared_input(context, path).is_none() {
        return Ok(None);
    }
    Ok(Some(Candidate { witness, span: expression.span, divisor: path.clone() }))
}

fn source_witness(context: &RuleContext<'_, '_, '_>, witness: NodeId) -> Option<ExprId> {
    let node = context.facts().cfg().node(witness)?;
    let CfgNodeKind::Witness { target, value } = &node.kind else { return None };
    let origin = node.origin?;
    let effect = context
        .hir()
        .block(origin.block)
        .and_then(|block| block.effects.get(origin.effect_index))?;
    let SourceSignalAssignment::Witness { target: source, value: written } =
        effect.signal_assignment()?
    else {
        return None;
    };
    (source == target && written == *value).then_some(*value)
}
