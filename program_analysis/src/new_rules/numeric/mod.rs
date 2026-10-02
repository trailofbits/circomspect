//! Numeric and expression warning family over certified HIR facts.

mod control;
mod division;
mod expression;

use parser::hir::{DefinitionRef, Expr, ExprId};
use parser::new_frontend::Span;

use crate::hir_facts::{FieldValue, Range};
use crate::interprocedural::ContextOrigin;
use crate::new_rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult, ScopedAbstention};

pub const KINDS: &[RuleKind] = &[
    RuleKind::BitwiseComplement,
    RuleKind::Bn254SpecificCircuit,
    RuleKind::ConstantConditional,
    RuleKind::FieldArithmetic,
    RuleKind::FieldComparison,
    RuleKind::NonstrictBinaryConversion,
    RuleKind::UnconstrainedDivision,
];

struct NumericRule(RuleKind);

impl Rule for NumericRule {
    fn kind(&self) -> RuleKind {
        self.0
    }

    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
        match self.0 {
            RuleKind::BitwiseComplement => expression::complement(context),
            RuleKind::Bn254SpecificCircuit => expression::bn254_constant(context),
            RuleKind::ConstantConditional => control::constant_conditional(context),
            RuleKind::FieldArithmetic => expression::field_arithmetic(context),
            RuleKind::FieldComparison => expression::field_comparison(context),
            RuleKind::UnconstrainedDivision => division::unconstrained_division(context),
            RuleKind::NonstrictBinaryConversion => {
                let mut result = RuleResult::default();
                if let Some(span) = definition_span(context) {
                    abstain(
                        context,
                        &mut result,
                        RuleKind::NonstrictBinaryConversion,
                        span,
                        AbstentionReason::UnsupportedConstruct,
                    );
                }
                result
            }
            RuleKind::SignalAssignment
            | RuleKind::RedundantWitnessAssignment
            | RuleKind::UnconstrainedSignal
            | RuleKind::UnconstrainedLessThan
            | RuleKind::UnusedVariableValue
            | RuleKind::UnusedParameterValue
            | RuleKind::SideEffectFreeAssignment
            | RuleKind::UnusedOutputSignal
            | RuleKind::Complexity
            | RuleKind::TooManyArguments
            | RuleKind::IncompleteCoverage => RuleResult::default(),
        }
    }
}

static COMPLEMENT: NumericRule = NumericRule(RuleKind::BitwiseComplement);
static BN254: NumericRule = NumericRule(RuleKind::Bn254SpecificCircuit);
static CONDITIONAL: NumericRule = NumericRule(RuleKind::ConstantConditional);
static ARITHMETIC: NumericRule = NumericRule(RuleKind::FieldArithmetic);
static COMPARISON: NumericRule = NumericRule(RuleKind::FieldComparison);
static CONVERSION: NumericRule = NumericRule(RuleKind::NonstrictBinaryConversion);
static DIVISION: NumericRule = NumericRule(RuleKind::UnconstrainedDivision);
static RULES: [&dyn Rule; 7] =
    [&COMPLEMENT, &BN254, &CONDITIONAL, &ARITHMETIC, &COMPARISON, &CONVERSION, &DIVISION];

/// Numeric rules enter the registry in this family's declared order.
pub fn rules() -> &'static [&'static dyn Rule] {
    &RULES
}

pub(super) fn definition_span(context: &RuleContext<'_, '_, '_>) -> Option<Span> {
    match context.call_context().definition() {
        DefinitionRef::Function(id) => context.hir().function(id).map(|item| item.span),
        DefinitionRef::Template(id) => context.hir().template(id).map(|item| item.span),
        DefinitionRef::Bus(id) => context.hir().bus(id).map(|item| item.span),
    }
}

pub(super) fn contained(inner: Span, outer: Span) -> bool {
    inner.source() == outer.source() && inner.start() >= outer.start() && inner.end() <= outer.end()
}

pub(super) fn expressions<'a>(
    context: &'a RuleContext<'_, '_, '_>,
) -> impl Iterator<Item = &'a Expr> {
    let span = definition_span(context);
    context
        .hir()
        .expressions()
        .iter()
        .filter(move |expression| span.is_some_and(|span| contained(expression.span, span)))
}

pub(super) fn abstain(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    kind: RuleKind,
    span: Span,
    reason: AbstentionReason,
) {
    result.add_abstention(ScopedAbstention {
        kind,
        context: context.call_context().clone(),
        span,
        reason,
    });
}

pub(super) fn reachable(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    kind: RuleKind,
    expression: &Expr,
) -> bool {
    let fact = context.facts().reachable_expression(expression.id);
    if let Some(value) = fact.certified() {
        return *value;
    }
    let reason = AbstentionReason::LocalFacts(fact.unavailable().cloned().unwrap_or_default());
    abstain(context, result, kind, expression.span, reason);
    false
}

pub(super) fn exact_value(
    context: &RuleContext<'_, '_, '_>,
    expression: ExprId,
) -> Result<FieldValue, AbstentionReason> {
    let fact = context.facts().range(expression);
    match fact.certified() {
        Some(Range::Exact(value)) => Ok(value.clone()),
        Some(Range::Unreachable | Range::Canonical) => match context.origin() {
            ContextOrigin::SymbolicRoot => Err(AbstentionReason::SymbolicParameters),
            ContextOrigin::Main(_) | ContextOrigin::Call(_) => {
                Err(AbstentionReason::UnsupportedConstruct)
            }
        },
        None => Err(AbstentionReason::LocalFacts(fact.unavailable().cloned().unwrap_or_default())),
    }
}

pub(super) fn exact_pair(
    context: &RuleContext<'_, '_, '_>,
    left: ExprId,
    right: ExprId,
) -> Result<(FieldValue, FieldValue), AbstentionReason> {
    Ok((exact_value(context, left)?, exact_value(context, right)?))
}
