use std::collections::BTreeSet;

use parser::hir::{DefinitionRef, Port, PortSchema};
use parser::new_frontend::{PortDirection, Span};

use crate::hir_facts::NoBitAmbiguityCertificate;
use crate::hir_facts::{AccessHandle, BitAmbiguity, BitAmbiguityOutcome};
use crate::interprocedural::{SummaryBlocker, SummaryFact};
use crate::new_rules::numeric::abstain;
use crate::new_rules::{AbstentionReason, RuleContext, RuleKind, RuleResult};

const MAX_BITS: usize = 512;
const MAX_CANDIDATE_PAIRS: usize = 32;

enum CandidateDecision {
    Emitted,
    Continue,
}

pub(super) fn nonstrict_binary_conversion(context: &RuleContext<'_, '_, '_>) -> RuleResult {
    let mut result = RuleResult::default();
    let Some((template_span, inputs, outputs)) = candidate_ports(context) else {
        return result;
    };
    let Some(count) = inputs.len().checked_mul(outputs.len()) else {
        abstain_budget(context, &mut result, template_span);
        return result;
    };
    if count > MAX_CANDIDATE_PAIRS {
        abstain_budget(context, &mut result, template_span);
        return result;
    }
    for output in outputs {
        inspect_output(context, &mut result, &inputs, output);
    }
    result
}

fn candidate_ports<'a>(
    context: &'a RuleContext<'_, '_, '_>,
) -> Option<(Span, Vec<&'a Port>, Vec<&'a Port>)> {
    let DefinitionRef::Template(id) = context.call_context().definition() else {
        return None;
    };
    let template = context.hir().template(id)?;
    let mut inputs = Vec::new();
    let mut outputs = Vec::new();
    for id in &template.ports {
        let Some(port) = context.hir().port(*id) else { continue };
        let Some(symbol) = context.hir().symbol(port.symbol) else { continue };
        if port.schema != PortSchema::Signal {
            continue;
        }
        if port.direction == Some(PortDirection::Input) && symbol.rank == 0 {
            inputs.push(port);
        } else if port.direction == Some(PortDirection::Output) && symbol.rank == 1 {
            outputs.push(port);
        }
    }
    if inputs.is_empty() || outputs.is_empty() {
        return None;
    }
    Some((template.span, inputs, outputs))
}

fn inspect_output(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    inputs: &[&Port],
    output: &Port,
) {
    let bits = match bit_handles(context, output) {
        Ok(bits) => bits,
        Err(reason) => {
            abstain(context, result, RuleKind::NonstrictBinaryConversion, output.span, reason);
            return;
        }
    };
    for input in inputs {
        let Ok(input_handle) = context.facts().port_handle(input.id, &[]) else {
            abstain(
                context,
                result,
                RuleKind::NonstrictBinaryConversion,
                input.span,
                AbstentionReason::UnsupportedConstruct,
            );
            continue;
        };
        let summary = context.template_bit_ambiguity_handles(&input_handle, &bits);
        match emit_or_abstain(context, result, input, output, &summary) {
            CandidateDecision::Emitted => break,
            CandidateDecision::Continue => {}
        }
    }
}

fn bit_handles(
    context: &RuleContext<'_, '_, '_>,
    output: &Port,
) -> Result<Vec<AccessHandle>, AbstentionReason> {
    let bounds = context
        .facts()
        .checked_symbol_dimensions(output.symbol)
        .map_err(|_| AbstentionReason::UnsupportedConstruct)?;
    let Some(&width) = bounds.first() else { return Err(AbstentionReason::UnsupportedConstruct) };
    if width == 0 || width > MAX_BITS {
        return Err(AbstentionReason::Summary(BTreeSet::from([SummaryBlocker::ContextBudget])));
    }
    let mut bits = Vec::with_capacity(width);
    for index in 0..width {
        let handle = context
            .facts()
            .port_handle(output.id, &[index])
            .map_err(|_| AbstentionReason::UnsupportedConstruct)?;
        bits.push(handle);
    }
    Ok(bits)
}

fn emit_or_abstain(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    input: &Port,
    output: &Port,
    summary: &SummaryFact<BitAmbiguityOutcome>,
) -> CandidateDecision {
    let Some(outcome) = summary.certified() else {
        let reason = AbstentionReason::Summary(summary.unavailable().cloned().unwrap_or_default());
        abstain(context, result, RuleKind::NonstrictBinaryConversion, output.span, reason);
        return CandidateDecision::Continue;
    };
    match outcome {
        BitAmbiguityOutcome::Proved(proof) => {
            emit(context, result, input, output, proof);
            CandidateDecision::Emitted
        }
        BitAmbiguityOutcome::NoCertificate(
            NoBitAmbiguityCertificate::NoMatchingDecomposition
            | NoBitAmbiguityCertificate::WidthBelowFieldModulus
            | NoBitAmbiguityCertificate::CandidatesRejected,
        ) => CandidateDecision::Continue,
    }
}

fn emit(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    input: &Port,
    output: &Port,
    proof: &BitAmbiguity,
) {
    let representations = proof.representations();
    let message = format!(
        concat!(
            "The same field input {} on {} admits distinct {}-bit vectors encoding integers ",
            "{} and {} within the complete checked generated constraints."
        ),
        proof.input_value().as_bigint(),
        context.facts().curve(),
        proof.decomposition().bits().len(),
        representations[0].integer(),
        representations[1].integer(),
    );
    let finding = context
        .finding(
            RuleKind::NonstrictBinaryConversion,
            message,
            output.span,
            "Two checked bit representations".into(),
        )
        .with_secondary(input.span, "Shared field input".into());
    result.add_finding(finding);
}

fn abstain_budget(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    span: parser::new_frontend::Span,
) {
    abstain(
        context,
        result,
        RuleKind::NonstrictBinaryConversion,
        span,
        AbstentionReason::Summary(BTreeSet::from([SummaryBlocker::ContextBudget])),
    );
}
