use std::collections::BTreeSet;

use parser::hir::{DefinitionRef, Port, PortSchema};
use parser::frontend::{PortDirection, Span};

use crate::hir_facts::NoBitAmbiguityCertificate;
use crate::hir_facts::{
    RankOnePortError, AccessHandle, BitAmbiguity, BitAmbiguityOutcome, BitRepresentation,
    FieldValue,
};
use crate::interprocedural::{
    CallSite, ComponentBitAmbiguity, ComponentBitAmbiguityOutcome, SummaryBlocker, SummaryFact,
};
use crate::rules::{AbstentionReason, RuleContext, RuleKind, RuleResult};

const MAX_BITS: usize = 512;
const MAX_CANDIDATE_PAIRS: usize = 32;

enum CandidateDecision {
    Emitted,
    Continue,
}

struct CalledConversion<'a> {
    span: Span,
    input: &'a Port,
    output: &'a Port,
}

pub(super) fn nonstrict_binary_conversion(context: &RuleContext<'_, '_, '_>) -> RuleResult {
    let mut result = RuleResult::default();
    if let Some((template_span, inputs, outputs)) =
        candidate_ports(context, context.call_context().definition())
    {
        if candidate_count(&inputs, &outputs) {
            for output in outputs {
                inspect_output(context, &mut result, &inputs, output);
            }
        } else {
            abstain_budget(context, &mut result, template_span);
        }
    }
    inspect_called_conversions(context, &mut result);
    result
}

fn candidate_ports<'a>(
    context: &'a RuleContext<'_, '_, '_>,
    definition: DefinitionRef,
) -> Option<(Span, Vec<&'a Port>, Vec<&'a Port>)> {
    let DefinitionRef::Template(id) = definition else {
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

fn candidate_count(inputs: &[&Port], outputs: &[&Port]) -> bool {
    inputs.len().checked_mul(outputs.len()).is_some_and(|count| count <= MAX_CANDIDATE_PAIRS)
}

fn inspect_called_conversions(context: &RuleContext<'_, '_, '_>, result: &mut RuleResult) {
    for site in context.call_sites() {
        let Some(definition) = site.resolved() else { continue };
        let Some((_, inputs, outputs)) = candidate_ports(context, definition) else { continue };
        if !candidate_count(&inputs, &outputs) {
            abstain_budget(context, result, site.span);
            continue;
        }
        for output in outputs {
            inspect_called_output(context, result, site, &inputs, output);
        }
    }
}

fn inspect_called_output(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    site: &CallSite,
    inputs: &[&Port],
    output: &Port,
) {
    let applied = match context.applied_component_first_output(site.id(), output.id) {
        Ok(None) => return,
        Ok(Some(summary)) => summary,
        Err(blocker) => {
            result.add_abstention(context.abstention(
                RuleKind::NonstrictBinaryConversion,
                site.span,
                AbstentionReason::Call(BTreeSet::from([blocker])),
            ));
            return;
        }
    };
    let Some(applied) = applied.certified() else {
        let reason = AbstentionReason::Summary(applied.unavailable().cloned().unwrap_or_default());
        result.add_abstention(context.abstention(
            RuleKind::NonstrictBinaryConversion,
            site.span,
            reason,
        ));
        return;
    };
    for input in inputs {
        let summary = context.component_bit_ambiguity_ports(applied, input.id, output.id);
        let candidate = CalledConversion { span: site.span, input, output };
        match emit_called_or_abstain(context, result, &candidate, &summary) {
            CandidateDecision::Emitted => break,
            CandidateDecision::Continue => {}
        }
    }
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
            result.add_abstention(context.abstention(
                RuleKind::NonstrictBinaryConversion,
                output.span,
                reason,
            ));
            return;
        }
    };
    for input in inputs {
        let Ok(input_handle) = context.facts().port_handle(input.id, &[]) else {
            result.add_abstention(context.abstention(
                RuleKind::NonstrictBinaryConversion,
                input.span,
                AbstentionReason::UnsupportedConstruct,
            ));
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
    context.facts().rank_one_port_handles(output, MAX_BITS).map_err(|error| match error {
        RankOnePortError::WidthLimit => {
            AbstentionReason::Summary(BTreeSet::from([SummaryBlocker::ContextBudget]))
        }
        RankOnePortError::InvalidShape(_)
        | RankOnePortError::InvalidRank
        | RankOnePortError::InvalidHandle(_) => AbstentionReason::UnsupportedConstruct,
    })
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
        result.add_abstention(context.abstention(
            RuleKind::NonstrictBinaryConversion,
            output.span,
            reason,
        ));
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

fn emit_called_or_abstain(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    candidate: &CalledConversion<'_>,
    summary: &SummaryFact<ComponentBitAmbiguityOutcome>,
) -> CandidateDecision {
    let Some(outcome) = summary.certified() else {
        let reason = AbstentionReason::Summary(summary.unavailable().cloned().unwrap_or_default());
        result.add_abstention(context.abstention(
            RuleKind::NonstrictBinaryConversion,
            candidate.span,
            reason,
        ));
        return CandidateDecision::Continue;
    };
    match outcome {
        ComponentBitAmbiguityOutcome::Proved(proof) => {
            emit_called(context, result, candidate, proof);
            CandidateDecision::Emitted
        }
        ComponentBitAmbiguityOutcome::NoCertificate(
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
    let message = ambiguity_message(
        context,
        proof.input_value(),
        proof.decomposition().bits().len(),
        proof.representations(),
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

fn emit_called(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    candidate: &CalledConversion<'_>,
    proof: &ComponentBitAmbiguity,
) {
    let message = format!(
        "{} The complete checked parent and child constraints admit both models.",
        ambiguity_message(
            context,
            proof.input_value(),
            proof.decomposition().bits().len(),
            proof.representations(),
        )
    );
    let finding = context
        .finding(
            RuleKind::NonstrictBinaryConversion,
            message,
            candidate.span,
            "Called conversion with two checked bit representations".into(),
        )
        .with_secondary(candidate.input.span, "Child input port".into())
        .with_secondary(candidate.output.span, "Child bit output port".into());
    result.add_finding(finding);
}

fn ambiguity_message(
    context: &RuleContext<'_, '_, '_>,
    input: &FieldValue,
    width: usize,
    representations: &[BitRepresentation; 2],
) -> String {
    format!(
        concat!(
            "The same field input {} on {} admits distinct {}-bit vectors encoding integers ",
            "{} and {} within the complete checked generated constraints."
        ),
        input.as_bigint(),
        context.facts().curve(),
        width,
        representations[0].integer(),
        representations[1].integer(),
    )
}

fn abstain_budget(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    span: parser::frontend::Span,
) {
    result.add_abstention(context.abstention(
        RuleKind::NonstrictBinaryConversion,
        span,
        AbstentionReason::Summary(BTreeSet::from([SummaryBlocker::ContextBudget])),
    ));
}

#[cfg(test)]
mod tests;
