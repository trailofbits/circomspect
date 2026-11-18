//! Main public inputs that have no generated constraint incidence.

use std::collections::BTreeSet;

use parser::frontend::PortDirection;
use parser::hir::{DefinitionRef, PortId, PortSchema, TemplateId};

use crate::hir_facts::Incidence;
use crate::rules::constraints::output_completeness::port_indices;
use crate::rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult};

pub(super) struct UnusedPublicInput;

impl Rule for UnusedPublicInput {
    fn kind(&self) -> RuleKind {
        RuleKind::UnusedPublicInput
    }

    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
        let mut result = RuleResult::default();
        let Some(main) = context.main() else { return result };
        let DefinitionRef::Template(template) = context.call_context().definition() else {
            return result;
        };
        if let Err(blocker) = context.validated_definition() {
            result.add_abstention(context.abstention(
                self.kind(),
                main.span,
                AbstentionReason::Summary(BTreeSet::from([blocker])),
            ));
            return result;
        }
        let mut seen = BTreeSet::new();
        for declared in &main.public {
            let Some(port) = find_input_port(context, template, &declared.name) else {
                result.add_abstention(context.abstention(
                    self.kind(),
                    declared.span,
                    AbstentionReason::UnsupportedConstruct,
                ));
                continue;
            };
            if seen.insert(port) {
                inspect_port(context, port, &mut result);
            }
        }
        result
    }
}

fn find_input_port(
    context: &RuleContext<'_, '_, '_>,
    template: TemplateId,
    name: &str,
) -> Option<PortId> {
    context.hir().template(template)?.ports.iter().copied().find(|id| {
        let Some(port) = context.hir().port(*id) else { return false };
        port.direction == Some(PortDirection::Input)
            && context.hir().symbol(port.symbol).is_some_and(|symbol| symbol.name == name)
    })
}

fn inspect_port(context: &RuleContext<'_, '_, '_>, id: PortId, result: &mut RuleResult) {
    let Some(port) = context.hir().port(id) else { return };
    if port.schema != PortSchema::Signal {
        abstain(context, port.span, result);
        return;
    }
    let Some(symbol) = context.hir().symbol(port.symbol) else { return };
    let Some(indices) = port_indices(context, port.symbol) else {
        abstain(context, port.span, result);
        return;
    };
    for index in indices {
        let Some(summary) = context.template_port(id, &index) else { return };
        match summary.as_result() {
            Ok(summary) => {
                match summary.incidence() {
                    Incidence::Zero => {
                        let path = format_path(&symbol.name, &index);
                        result.add_finding(context.finding(
                        RuleKind::UnusedPublicInput,
                        format!("Public input `{path}` has no generated constraint."),
                        port.span,
                        format!("The public input `{path}` is independent of the proof constraints."),
                    ));
                    }
                    Incidence::May => abstain(context, port.span, result),
                    Incidence::Must => {}
                }
            }
            Err(blockers) => result.add_abstention(context.abstention(
                RuleKind::UnusedPublicInput,
                port.span,
                AbstentionReason::Summary(blockers.clone()),
            )),
        }
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

fn abstain(
    context: &RuleContext<'_, '_, '_>,
    span: parser::frontend::Span,
    result: &mut RuleResult,
) {
    result.add_abstention(context.abstention(
        RuleKind::UnusedPublicInput,
        span,
        AbstentionReason::UnsupportedConstruct,
    ));
}
