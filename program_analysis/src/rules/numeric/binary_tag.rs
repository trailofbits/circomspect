//! Binary tag claims contradicted by a complete satisfying model.

use std::collections::BTreeSet;

use parser::frontend::PortDirection;
use parser::hir::{DefinitionRef, Symbol, SymbolKind, Template};

use crate::interprocedural::SummaryBlocker;
use crate::rules::{AbstentionReason, RuleContext, RuleKind, RuleResult};

pub(super) fn unproved_binary_tag(context: &RuleContext<'_, '_, '_>) -> RuleResult {
    let mut result = RuleResult::default();
    let DefinitionRef::Template(id) = context.call_context().definition() else { return result };
    let Some(template) = context.hir().template(id) else { return result };
    let candidates = candidate_symbols(context, template, &mut result);
    if candidates.is_empty() {
        return result;
    }
    if template.custom || template.external || context.main().is_none() {
        abstain_scope(context, template, &candidates, &mut result);
        return result;
    }
    let queries = context.template_generated_equations();
    let symbols: Vec<_> = candidates.iter().map(|symbol| symbol.id).collect();
    match queries.binary_tag_counterexamples(&symbols).as_result() {
        Ok(proofs) => {
            for proof in proofs {
                let Some(symbol) = context.hir().symbol(proof.symbol) else { continue };
                result.add_finding(context.finding(
                    RuleKind::UnprovedBinaryTag,
                    format!(
                    "`{}` has a `binary` tag, but value {} satisfies all {} generated constraints.",
                    symbol.name,
                    proof.value.as_bigint(),
                    proof.constraint_count,
                ),
                    symbol.span,
                    "The binary tag is not enforced by this constraint system.".into(),
                ));
            }
        }
        Err(blockers) => {
            for symbol in candidates {
                result.add_abstention(context.abstention(
                    RuleKind::UnprovedBinaryTag,
                    symbol.span,
                    AbstentionReason::Summary(blockers.clone()),
                ));
            }
        }
    }
    result
}

fn candidate_symbols<'a>(
    context: &'a RuleContext<'_, '_, '_>,
    template: &Template,
    result: &mut RuleResult,
) -> Vec<&'a Symbol> {
    let mut candidates = Vec::new();
    let inputs: BTreeSet<_> = template
        .ports
        .iter()
        .filter_map(|id| context.hir().port(*id))
        .filter(|port| port.direction == Some(PortDirection::Input))
        .map(|port| port.symbol)
        .collect();
    for symbol in context.hir().symbols() {
        if !super::contained(symbol.span, template.span) || !has_binary_tag(context, symbol) {
            continue;
        }
        if inputs.contains(&symbol.id) {
            continue;
        }
        if symbol.kind != SymbolKind::Signal || symbol.rank != 0 || !symbol.shape_checked {
            result.add_abstention(context.abstention(
                RuleKind::UnprovedBinaryTag,
                symbol.span,
                AbstentionReason::UnsupportedConstruct,
            ));
            continue;
        }
        candidates.push(symbol);
    }
    candidates
}

fn abstain_scope(
    context: &RuleContext<'_, '_, '_>,
    template: &Template,
    candidates: &[&Symbol],
    result: &mut RuleResult,
) {
    let reason = if template.custom || template.external {
        AbstentionReason::UnsupportedConstruct
    } else {
        AbstentionReason::Summary(BTreeSet::from([SummaryBlocker::ExternalSummary]))
    };
    for symbol in candidates {
        result.add_abstention(context.abstention(
            RuleKind::UnprovedBinaryTag,
            symbol.span,
            reason.clone(),
        ));
    }
}

fn has_binary_tag(context: &RuleContext<'_, '_, '_>, symbol: &Symbol) -> bool {
    symbol
        .tags
        .iter()
        .any(|tag| context.hir().symbol(*tag).is_some_and(|declared| declared.name == "binary"))
}
