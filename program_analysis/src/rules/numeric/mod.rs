//! Numeric and expression warning family over certified HIR facts.

mod control;
mod binary_tag;
mod bit_packing;
mod conversion;
mod division;
mod zero_divisor;
mod expression;

use std::collections::BTreeSet;

use parser::hir::{DefinitionRef, Expr, ExprId};
use parser::frontend::Span;

use crate::hir_facts::{FieldValue, Range};
use crate::interprocedural::ContextOrigin;
use crate::rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult};

pub const KINDS: &[RuleKind] = &[
    RuleKind::BitwiseComplement,
    RuleKind::Bn254SpecificCircuit,
    RuleKind::ConstantConditional,
    RuleKind::FieldArithmetic,
    RuleKind::FieldComparison,
    RuleKind::NonstrictBinaryConversion,
    RuleKind::UnconstrainedDivision,
    RuleKind::NonInjectiveBitPacking,
    RuleKind::FeasibleZeroDivisor,
    RuleKind::UnprovedBinaryTag,
];

enum NumericRule {
    BitwiseComplement,
    Bn254SpecificCircuit,
    ConstantConditional,
    FieldArithmetic,
    FieldComparison,
    NonstrictBinaryConversion,
    UnconstrainedDivision,
    NonInjectiveBitPacking,
    FeasibleZeroDivisor,
    UnprovedBinaryTag,
}

impl Rule for NumericRule {
    fn kind(&self) -> RuleKind {
        match self {
            Self::BitwiseComplement => RuleKind::BitwiseComplement,
            Self::Bn254SpecificCircuit => RuleKind::Bn254SpecificCircuit,
            Self::ConstantConditional => RuleKind::ConstantConditional,
            Self::FieldArithmetic => RuleKind::FieldArithmetic,
            Self::FieldComparison => RuleKind::FieldComparison,
            Self::NonstrictBinaryConversion => RuleKind::NonstrictBinaryConversion,
            Self::UnconstrainedDivision => RuleKind::UnconstrainedDivision,
            Self::NonInjectiveBitPacking => RuleKind::NonInjectiveBitPacking,
            Self::FeasibleZeroDivisor => RuleKind::FeasibleZeroDivisor,
            Self::UnprovedBinaryTag => RuleKind::UnprovedBinaryTag,
        }
    }

    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
        if let Err(blocker) = context.check_warning_execution_scope() {
            let mut result = RuleResult::default();
            if let Some(span) = definition_span(context) {
                result.add_abstention(context.abstention(
                    self.kind(),
                    span,
                    AbstentionReason::Summary(BTreeSet::from([blocker])),
                ));
            }
            return result;
        }
        match self {
            Self::BitwiseComplement => expression::complement(context),
            Self::Bn254SpecificCircuit => expression::bn254_constant(context),
            Self::ConstantConditional => control::constant_conditional(context),
            Self::FieldArithmetic => expression::field_arithmetic(context),
            Self::FieldComparison => expression::field_comparison(context),
            Self::UnconstrainedDivision => division::unconstrained_division(context),
            Self::NonstrictBinaryConversion => conversion::nonstrict_binary_conversion(context),
            Self::NonInjectiveBitPacking => bit_packing::noninjective_bit_packing(context),
            Self::FeasibleZeroDivisor => zero_divisor::feasible_zero_divisor(context),
            Self::UnprovedBinaryTag => binary_tag::unproved_binary_tag(context),
        }
    }
}

static COMPLEMENT: NumericRule = NumericRule::BitwiseComplement;
static BN254: NumericRule = NumericRule::Bn254SpecificCircuit;
static CONDITIONAL: NumericRule = NumericRule::ConstantConditional;
static ARITHMETIC: NumericRule = NumericRule::FieldArithmetic;
static COMPARISON: NumericRule = NumericRule::FieldComparison;
static CONVERSION: NumericRule = NumericRule::NonstrictBinaryConversion;
static DIVISION: NumericRule = NumericRule::UnconstrainedDivision;
static BIT_PACKING: NumericRule = NumericRule::NonInjectiveBitPacking;
static ZERO_DIVISOR: NumericRule = NumericRule::FeasibleZeroDivisor;
static BINARY_TAG: NumericRule = NumericRule::UnprovedBinaryTag;
static RULES: [&dyn Rule; 10] = [
    &COMPLEMENT,
    &BN254,
    &CONDITIONAL,
    &ARITHMETIC,
    &COMPARISON,
    &CONVERSION,
    &DIVISION,
    &BIT_PACKING,
    &ZERO_DIVISOR,
    &BINARY_TAG,
];

/// Numeric rules enter the registry in this family's declared order.
#[must_use]
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

pub(super) fn reachable(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    kind: RuleKind,
    expression: &Expr,
) -> bool {
    let fact = context.facts().reachable_expression(expression.id);
    match fact.into_result() {
        Ok(value) => value,
        Err(blockers) => {
            result.add_abstention(context.abstention(
                kind,
                expression.span,
                AbstentionReason::LocalFacts(blockers),
            ));
            false
        }
    }
}

pub(super) fn exact_value(
    context: &RuleContext<'_, '_, '_>,
    expression: ExprId,
) -> Result<FieldValue, AbstentionReason> {
    let fact = context.facts().range(expression);
    match fact.into_result() {
        Ok(Range::Exact(value)) => Ok(value),
        Ok(Range::Unreachable | Range::Canonical) => match context.origin() {
            ContextOrigin::SymbolicRoot => Err(AbstentionReason::SymbolicParameters),
            ContextOrigin::Main(_) | ContextOrigin::Call(_) => {
                Err(AbstentionReason::UnsupportedConstruct)
            }
        },
        Err(blockers) => Err(AbstentionReason::LocalFacts(blockers)),
    }
}

pub(super) fn exact_pair(
    context: &RuleContext<'_, '_, '_>,
    left: ExprId,
    right: ExprId,
) -> Result<(FieldValue, FieldValue), AbstentionReason> {
    Ok((exact_value(context, left)?, exact_value(context, right)?))
}
