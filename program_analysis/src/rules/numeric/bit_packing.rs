//! Checked collisions in Boolean input vectors packed into one field output.

use std::collections::BTreeSet;

use parser::frontend::{PortDirection, Span};
use parser::hir::{DefinitionRef, Port, PortSchema};

use crate::hir_facts::{BitAmbiguityOutcome, NoBitAmbiguityCertificate, RankOnePortError};
use crate::interprocedural::{ContextOrigin, SummaryBlocker, SummaryFact};
use crate::rules::{AbstentionReason, RuleContext, RuleKind, RuleResult};

const MAX_BITS: usize = 512;
const MAX_PAIRS: usize = 32;

pub(super) fn noninjective_bit_packing(context: &RuleContext<'_, '_, '_>) -> RuleResult {
    let mut result = RuleResult::default();
    if context.main().is_none() {
        abstain_called(context, &mut result);
        return result;
    }
    let Some((span, inputs, outputs)) = candidate_ports(context) else { return result };
    if !inputs.len().checked_mul(outputs.len()).is_some_and(|count| count <= MAX_PAIRS) {
        result.add_abstention(context.abstention(
            RuleKind::NonInjectiveBitPacking,
            span,
            AbstentionReason::Summary(BTreeSet::from([SummaryBlocker::ContextBudget])),
        ));
        return result;
    }
    for input in inputs {
        inspect_input(context, input, &outputs, &mut result);
    }
    result
}

fn abstain_called(context: &RuleContext<'_, '_, '_>, result: &mut RuleResult) {
    let ContextOrigin::Call(_) = context.origin() else { return };
    let Some((span, _, _)) = candidate_ports(context) else { return };
    result.add_abstention(context.abstention(
        RuleKind::NonInjectiveBitPacking,
        span,
        AbstentionReason::Summary(BTreeSet::from([SummaryBlocker::ExternalSummary])),
    ));
}

fn candidate_ports<'a>(
    context: &'a RuleContext<'_, '_, '_>,
) -> Option<(Span, Vec<&'a Port>, Vec<&'a Port>)> {
    let DefinitionRef::Template(id) = context.call_context().definition() else { return None };
    let template = context.hir().template(id)?;
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();
    for id in &template.ports {
        let Some(port) = context.hir().port(*id) else { continue };
        let Some(symbol) = context.hir().symbol(port.symbol) else { continue };
        if port.schema != PortSchema::Signal {
            continue;
        }
        match (port.direction, symbol.rank) {
            (Some(PortDirection::Input), 1) => inputs.push(port),
            (Some(PortDirection::Output), 0) => outputs.push(port),
            (None | Some(PortDirection::Input | PortDirection::Output), _) => {}
        }
    }
    if inputs.is_empty() || outputs.is_empty() {
        return None;
    }
    Some((template.span, inputs, outputs))
}

fn inspect_input(
    context: &RuleContext<'_, '_, '_>,
    input: &Port,
    outputs: &[&Port],
    result: &mut RuleResult,
) {
    let bits = match context.facts().rank_one_port_handles(input, MAX_BITS) {
        Ok(bits) => bits,
        Err(RankOnePortError::WidthLimit) => {
            result.add_abstention(context.abstention(
                RuleKind::NonInjectiveBitPacking,
                input.span,
                AbstentionReason::Summary(BTreeSet::from([SummaryBlocker::ContextBudget])),
            ));
            return;
        }
        Err(
            RankOnePortError::InvalidShape(_)
            | RankOnePortError::InvalidRank
            | RankOnePortError::InvalidHandle(_),
        ) => return,
    };
    for output in outputs {
        let Ok(packed) = context.facts().port_handle(output.id, &[]) else { continue };
        let summary = context.template_bit_packing_collision_handles(&packed, &bits);
        inspect_pair(context, input, output, &summary, result);
    }
}

fn inspect_pair(
    context: &RuleContext<'_, '_, '_>,
    input: &Port,
    output: &Port,
    summary: &SummaryFact<BitAmbiguityOutcome>,
    result: &mut RuleResult,
) {
    match summary.as_result() {
        Ok(BitAmbiguityOutcome::Proved(proof)) => {
            let name =
                context.hir().symbol(output.symbol).map_or("packed value", |item| &item.name);
            let representations = proof.representations();
            let message = format!(
                "Distinct Boolean bit vectors encoding {} and {} both produce `{name}` = {} \
                 in the checked generated constraints.",
                representations[0].integer(),
                representations[1].integer(),
                proof.input_value().as_bigint(),
            );
            result.add_finding(context.finding(
                RuleKind::NonInjectiveBitPacking,
                message,
                output.span,
                "This bit packing admits two checked input vectors with the same field value."
                    .into(),
            ).with_secondary(input.span, "These Boolean bits have two valid encodings.".into()));
        }
        Ok(BitAmbiguityOutcome::NoCertificate(
            NoBitAmbiguityCertificate::NoMatchingDecomposition
            | NoBitAmbiguityCertificate::WidthBelowFieldModulus
            | NoBitAmbiguityCertificate::CandidatesRejected,
        )) => {}
        Err(blockers) => result.add_abstention(context.abstention(
            RuleKind::NonInjectiveBitPacking,
            output.span,
            AbstentionReason::Summary(blockers.clone()),
        )),
    }
}
