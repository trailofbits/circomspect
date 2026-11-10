use parser::hir::DefinitionRef;
use parser::frontend::Span;

use crate::interprocedural::{ContextOrigin, ProjectOutputStatus, ProjectOutputUse, SummaryBlocker};
use crate::rules::uses::{definition_span, summary_abstain, summary_reason};
use crate::rules::{AbstentionReason, RuleContext, RuleKind, RuleResult};

pub(super) fn unused_outputs(context: &RuleContext<'_, '_, '_>, result: &mut RuleResult) {
    let DefinitionRef::Template(_) = context.call_context().definition() else { return };
    match context.origin() {
        ContextOrigin::Main(_) => closed_outputs(context, result),
        ContextOrigin::SymbolicRoot => symbolic_outputs(context, result),
        ContextOrigin::Call(_) => {}
    }
}

fn closed_outputs(context: &RuleContext<'_, '_, '_>, result: &mut RuleResult) {
    let kind = RuleKind::UnusedOutputSignal;
    let closure = context.closed_project_output_uses();
    let uses = match closure.as_result() {
        Ok(uses) => uses,
        Err(blockers) => {
            if let Some(span) = definition_span(context) {
                summary_abstain(context, kind, span, blockers, result);
            }
            return;
        }
    };
    let mut reported: Vec<&ProjectOutputUse> = Vec::new();
    for use_proof in uses {
        if use_proof.status() == ProjectOutputStatus::Read {
            continue;
        }
        if reported.iter().any(|prior| {
            prior.instance_path() == use_proof.instance_path()
                && prior.handle() == use_proof.handle()
        }) {
            continue;
        }
        report_output(context, use_proof, result);
        reported.push(use_proof);
    }
}

fn symbolic_outputs(context: &RuleContext<'_, '_, '_>, result: &mut RuleResult) {
    let kind = RuleKind::UnusedOutputSignal;
    let outputs = context.exact_component_outputs();
    let outputs = match outputs.as_result() {
        Ok(outputs) => outputs,
        Err(blockers) => {
            if let Some(span) = definition_span(context) {
                summary_abstain(context, kind, span, blockers, result);
            }
            return;
        }
    };
    for output in outputs {
        result.add_abstention(context.abstention(
            kind,
            output.source_span(),
            summary_reason(SummaryBlocker::UnsupportedContext),
        ));
    }
}

fn report_output(
    context: &RuleContext<'_, '_, '_>,
    use_proof: &ProjectOutputUse,
    result: &mut RuleResult,
) {
    let kind = RuleKind::UnusedOutputSignal;
    let span = use_proof.source_span();
    let Some(path) = output_path(context, use_proof) else {
        result.add_abstention(context.abstention(
            kind,
            span,
            AbstentionReason::UnsupportedConstruct,
        ));
        return;
    };
    let message = format!("Component output `{}` is never read", path.name);
    let mut finding = context.finding(kind, message, span, "unused output".into());
    for (name, source) in path.ancestors {
        finding = finding.with_secondary(source, format!("instance `{name}`"));
    }
    result.add_finding(finding);
}

struct OutputPath {
    name: String,
    ancestors: Vec<(String, Span)>,
}

fn output_path(context: &RuleContext<'_, '_, '_>, proof: &ProjectOutputUse) -> Option<OutputPath> {
    let mut segments = Vec::new();
    let mut ancestors = Vec::new();
    let steps = proof.instance_path();
    for (position, step) in steps.iter().enumerate() {
        let symbol = context.hir().symbol(step.target().root)?;
        let mut segment = symbol.name.clone();
        for index in step.indices() {
            segment.push('[');
            segment.push_str(&index.to_string());
            segment.push(']');
        }
        segments.push(segment);
        if position + 1 < steps.len() {
            let source = step.callee_evidence().call_path().last()?.span();
            ancestors.push((segments.join("."), source));
        }
    }
    let symbol = context.hir().symbol(proof.handle().path().terminal)?;
    let mut output = symbol.name.clone();
    for index in proof.output_indices()? {
        output.push('[');
        output.push_str(&index.to_string());
        output.push(']');
    }
    segments.push(output);
    Some(OutputPath { name: segments.join("."), ancestors })
}
