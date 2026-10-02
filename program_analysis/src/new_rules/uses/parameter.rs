use parser::hir::DefinitionRef;

use crate::new_rules::{RuleContext, RuleKind, RuleResult};
use crate::new_rules::uses::{local_abstain, validated};

pub(super) fn unused_parameters(context: &RuleContext<'_, '_, '_>, result: &mut RuleResult) {
    let kind = RuleKind::UnusedParameterValue;
    if !validated(context, kind, result) {
        return;
    }
    let parameters = match context.call_context().definition() {
        DefinitionRef::Function(id) => context.hir().function(id).map(|item| &item.parameters),
        DefinitionRef::Template(id) => context.hir().template(id).map(|item| &item.parameters),
        DefinitionRef::Bus(_) => None,
    };
    let Some(parameters) = parameters else { return };
    for parameter in parameters {
        let Some(symbol) = context.hir().symbol(*parameter) else { continue };
        let read = context.facts().parameter_read(*parameter);
        match read.certified() {
            Some(false) => {
                let message = format!("Parameter `{}` is never read in this context", symbol.name);
                result.add_finding(context.finding(
                    kind,
                    message,
                    symbol.span,
                    "unused parameter".into(),
                ));
            }
            Some(true) => {}
            None => local_abstain(context, kind, symbol.span, &read, result),
        }
    }
}
