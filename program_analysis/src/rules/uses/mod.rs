//! Dependency, side-effect, and output-use warning family.

mod assignment;
mod output;
mod parameter;

use std::collections::BTreeSet;

use parser::hir::DefinitionRef;
use parser::frontend::Span;

use crate::interprocedural::SummaryBlocker;
use crate::rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult};

pub const KINDS: &[RuleKind] = &[
    RuleKind::UnusedVariableValue,
    RuleKind::UnusedParameterValue,
    RuleKind::SideEffectFreeAssignment,
    RuleKind::UnusedOutputSignal,
];

enum UseRule {
    UnusedVariable,
    UnusedParameter,
    SideEffectFree,
    UnusedOutput,
}

static UNUSED_VARIABLE: UseRule = UseRule::UnusedVariable;
static UNUSED_PARAMETER: UseRule = UseRule::UnusedParameter;
static SIDE_EFFECT_FREE: UseRule = UseRule::SideEffectFree;
static UNUSED_OUTPUT: UseRule = UseRule::UnusedOutput;
static RULES: [&dyn Rule; 4] =
    [&UNUSED_VARIABLE, &UNUSED_PARAMETER, &SIDE_EFFECT_FREE, &UNUSED_OUTPUT];

/// Use and effect rules enter the registry in this family's declared order.
#[must_use]
pub fn rules() -> &'static [&'static dyn Rule] {
    &RULES
}

impl Rule for UseRule {
    fn kind(&self) -> RuleKind {
        match self {
            Self::UnusedVariable => RuleKind::UnusedVariableValue,
            Self::UnusedParameter => RuleKind::UnusedParameterValue,
            Self::SideEffectFree => RuleKind::SideEffectFreeAssignment,
            Self::UnusedOutput => RuleKind::UnusedOutputSignal,
        }
    }

    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
        let mut result = RuleResult::default();
        match self {
            Self::UnusedVariable => assignment::unused_values(context, &mut result),
            Self::UnusedParameter => parameter::unused_parameters(context, &mut result),
            Self::SideEffectFree => assignment::side_effect_free(context, &mut result),
            Self::UnusedOutput => output::unused_outputs(context, &mut result),
        }
        result
    }
}

fn validated(context: &RuleContext<'_, '_, '_>, kind: RuleKind, result: &mut RuleResult) -> bool {
    let validation =
        context.validated_definition().and_then(|_| context.check_warning_execution_scope());
    let Err(blocker) = validation else { return true };
    if let Some(span) = definition_span(context) {
        result.add_abstention(context.abstention(kind, span, summary_reason(blocker)));
    }
    false
}

fn definition_span(context: &RuleContext<'_, '_, '_>) -> Option<Span> {
    match context.call_context().definition() {
        DefinitionRef::Function(id) => context.hir().function(id).map(|item| item.name_span),
        DefinitionRef::Template(id) => context.hir().template(id).map(|item| item.name_span),
        DefinitionRef::Bus(id) => context.hir().bus(id).map(|item| item.name_span),
    }
}

fn summary_reason(blocker: SummaryBlocker) -> AbstentionReason {
    match blocker {
        SummaryBlocker::IncompleteDefinition => AbstentionReason::IncompleteDefinition,
        SummaryBlocker::ForeignDefinition
        | SummaryBlocker::ForeignCall
        | SummaryBlocker::WrongContext
        | SummaryBlocker::WrongArity { .. }
        | SummaryBlocker::UnprovenArgument(_)
        | SummaryBlocker::UnsupportedCallForm
        | SummaryBlocker::LocalFacts(_)
        | SummaryBlocker::UnsupportedContext
        | SummaryBlocker::InvalidAssignment(_)
        | SummaryBlocker::InvalidValueUse(_)
        | SummaryBlocker::WrongInstance
        | SummaryBlocker::DuplicateInstance
        | SummaryBlocker::SymbolicInstance
        | SummaryBlocker::MissingInputBinding
        | SummaryBlocker::DuplicateInputBinding
        | SummaryBlocker::WitnessOnlyInput
        | SummaryBlocker::ExternalSummary
        | SummaryBlocker::MissingReturn
        | SummaryBlocker::LocalAnalysis(_)
        | SummaryBlocker::RecursiveCycle
        | SummaryBlocker::ContextBudget => AbstentionReason::Summary(BTreeSet::from([blocker])),
    }
}

fn summary_abstain(
    context: &RuleContext<'_, '_, '_>,
    kind: RuleKind,
    span: Span,
    blockers: &BTreeSet<SummaryBlocker>,
    result: &mut RuleResult,
) {
    result.add_abstention(context.abstention(
        kind,
        span,
        AbstentionReason::Summary(blockers.clone()),
    ));
}
