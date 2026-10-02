use crate::interprocedural::{EnumeratedComponentOutput, ProjectOutputStatus};
use crate::new_rules::{RuleContext, RuleKind, RuleResult};
use crate::new_rules::uses::{abstain, definition_span, summary_abstain, summary_reason};

pub(super) fn unused_outputs(context: &RuleContext<'_, '_, '_>, result: &mut RuleResult) {
    let kind = RuleKind::UnusedOutputSignal;
    let outputs = context.exact_component_outputs();
    let Some(outputs) = outputs.certified() else {
        summary_abstain(context, kind, definition_span(context), &outputs, result);
        return;
    };
    for output in outputs {
        report_output(context, output, result);
    }
}

fn report_output(
    context: &RuleContext<'_, '_, '_>,
    output: &EnumeratedComponentOutput,
    result: &mut RuleResult,
) {
    let kind = RuleKind::UnusedOutputSignal;
    let span = output.source_span();
    let use_fact = context.closed_main_component_output_use(output.applied_port());
    let fact = match use_fact {
        Ok(fact) => fact,
        Err(blocker) => {
            abstain(result, context, kind, span, summary_reason(blocker));
            return;
        }
    };
    let Some(use_proof) = fact.certified() else {
        summary_abstain(context, kind, span, &fact, result);
        return;
    };
    if use_proof.status() != ProjectOutputStatus::Unused {
        return;
    }
    let port = output.applied_port().port_summary().port();
    let Some(port) = context.hir().port(port) else { return };
    let Some(symbol) = context.hir().symbol(port.symbol) else { return };
    let message = format!("Component output `{}` is never read", symbol.name);
    result.add_finding(context.finding(kind, message, span, "unused output".into()));
}
