//! Comparator diagnostics consume only complete provider-owned relation certificates.

use std::collections::BTreeSet;

use crate::interprocedural::ComparatorRangeViolation;
use crate::new_rules::constraints::abstain;
use crate::new_rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult};

pub(super) struct Comparator;

impl Rule for Comparator {
    fn kind(&self) -> RuleKind {
        RuleKind::UnconstrainedLessThan
    }

    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
        let mut result = RuleResult::default();
        let outputs = context.exact_component_outputs();
        let Some(outputs) = outputs.certified() else {
            if let Ok(header) = context.validated_header() {
                abstain(
                    context,
                    &mut result,
                    self.kind(),
                    header.name_span(),
                    AbstentionReason::Summary(outputs.unavailable().cloned().unwrap_or_default()),
                );
            }
            return result;
        };
        let mut emitted = BTreeSet::new();
        for output in outputs {
            let violations = context.component_comparator_range(output.applied_port());
            let Some(violations) = violations.certified() else {
                abstain(
                    context,
                    &mut result,
                    self.kind(),
                    output.source_span(),
                    AbstentionReason::Summary(
                        violations.unavailable().cloned().unwrap_or_default(),
                    ),
                );
                continue;
            };
            for violation in violations {
                if emitted.insert(violation.input().clone()) {
                    report(context, violation, &mut result);
                }
            }
        }
        result
    }
}

fn report(
    context: &RuleContext<'_, '_, '_>,
    proof: &ComparatorRangeViolation,
    result: &mut RuleResult,
) {
    let mut finding = context.finding(
        RuleKind::UnconstrainedLessThan,
        format!(
            "Comparator input {} is outside the proved safe range [0, {}).",
            proof.value().as_bigint(),
            proof.upper_bound()
        ),
        proof.binding_span(),
        "Generated equality fixes this comparator input".into(),
    );
    let mut spans = BTreeSet::new();
    for origin in proof.constraint_origins() {
        if !spans.insert((origin.span.source(), origin.span.start(), origin.span.end())) {
            continue;
        }
        finding =
            finding.with_secondary(origin.span, "Validated generated comparator constraint".into());
    }
    result.add_finding(finding);
}
