use std::cmp::Ordering;

use num_bigint::BigInt;
use num_traits::Zero;
use parser::hir::{DefinitionRef, ExprKind};
use parser::frontend::{BinaryOperator, UnaryOperator};
use program_structure::utils::constants::{Curve, UsefulConstants};

use crate::hir_facts::FieldContext;
use crate::interprocedural::CallOwner;
use crate::rules::{RuleContext, RuleKind, RuleResult};
use crate::rules::numeric::{exact_pair, expressions, reachable};

pub(super) fn complement(context: &RuleContext<'_, '_, '_>) -> RuleResult {
    let mut result = RuleResult::default();
    let constants = UsefulConstants::new(context.facts().curve());
    for expression in expressions(context) {
        let ExprKind::Unary { operator: UnaryOperator::Complement, .. } = &expression.kind else {
            continue;
        };
        if !reachable(context, &mut result, RuleKind::BitwiseComplement, expression) {
            continue;
        }
        let message = format!(
            concat!(
                "On {}, Circom complements the low {} bits and ",
                "reduces the result modulo the field prime."
            ),
            constants.curve(),
            constants.prime_size()
        );
        result.add_finding(context.finding(
            RuleKind::BitwiseComplement,
            message,
            expression.span,
            "This complement is evaluated in the selected field.".into(),
        ));
    }
    result
}

pub(super) fn bn254_constant(context: &RuleContext<'_, '_, '_>) -> RuleResult {
    let mut result = RuleResult::default();
    if context.facts().curve() == &Curve::Bn254 || !has_template_origin(context) {
        return result;
    }
    let bn254_prime = UsefulConstants::new(&Curve::Bn254).prime().clone();
    for expression in expressions(context) {
        let ExprKind::Number(text) = &expression.kind else { continue };
        let (digits, radix) =
            if let Some(hex) = text.strip_prefix("0x") { (hex, 16) } else { (text.as_str(), 10) };
        let Some(value) = BigInt::parse_bytes(digits.as_bytes(), radix) else { continue };
        if value != bn254_prime {
            continue;
        }
        if !reachable(context, &mut result, RuleKind::Bn254SpecificCircuit, expression) {
            continue;
        }
        let finding = context.finding(
            RuleKind::Bn254SpecificCircuit,
            format!(
                "This reachable literal is the BN254 field prime, but the selected curve is {}.",
                context.facts().curve()
            ),
            expression.span,
            "This literal is the BN254 field modulus.".into(),
        );
        result.add_finding(finding);
    }
    result
}

fn has_template_origin(context: &RuleContext<'_, '_, '_>) -> bool {
    if let DefinitionRef::Template(_) = context.call_context().definition() {
        return true;
    }
    context.call_path().iter().any(|site| {
        if let DefinitionRef::Template(_) = site.callee() {
            return true;
        }
        if let CallOwner::Definition(DefinitionRef::Template(_)) = site.owner() {
            return true;
        }
        false
    })
}

pub(super) fn field_arithmetic(context: &RuleContext<'_, '_, '_>) -> RuleResult {
    let mut result = RuleResult::default();
    let modulus = UsefulConstants::new(context.facts().curve()).prime().clone();
    for expression in expressions(context) {
        let ExprKind::Binary { operator, left, right } = &expression.kind else { continue };
        let is_arithmetic = *operator == BinaryOperator::Add
            || *operator == BinaryOperator::Subtract
            || *operator == BinaryOperator::Multiply;
        if !is_arithmetic || !reachable(context, &mut result, RuleKind::FieldArithmetic, expression)
        {
            continue;
        }
        let (left, right) = match exact_pair(context, *left, *right) {
            Ok(values) => values,
            Err(reason) => {
                result.add_abstention(context.abstention(
                    RuleKind::FieldArithmetic,
                    expression.span,
                    reason,
                ));
                continue;
            }
        };
        let unreduced = if *operator == BinaryOperator::Add {
            left.as_bigint() + right.as_bigint()
        } else if *operator == BinaryOperator::Subtract {
            left.as_bigint() - right.as_bigint()
        } else {
            left.as_bigint() * right.as_bigint()
        };
        if unreduced >= BigInt::zero() && unreduced < modulus {
            continue;
        }
        let field = FieldContext::for_curve(context.facts().curve().clone());
        let reduced = field.canonical(unreduced.clone());
        result.add_finding(context.finding(
            RuleKind::FieldArithmetic,
            format!(
                concat!(
                    "Exact operands produce {}; field arithmetic reduces it to ",
                    "{} modulo the selected prime."
                ),
                unreduced,
                reduced.as_bigint()
            ),
            expression.span,
            "This arithmetic wraps modulo the field prime.".into(),
        ));
    }
    result
}

pub(super) fn field_comparison(context: &RuleContext<'_, '_, '_>) -> RuleResult {
    let mut result = RuleResult::default();
    let field = FieldContext::for_curve(context.facts().curve().clone());
    for expression in expressions(context) {
        let ExprKind::Binary { operator, left, right } = &expression.kind else { continue };
        let is_comparison = *operator == BinaryOperator::Less
            || *operator == BinaryOperator::Greater
            || *operator == BinaryOperator::LessEqual
            || *operator == BinaryOperator::GreaterEqual;
        if !is_comparison || !reachable(context, &mut result, RuleKind::FieldComparison, expression)
        {
            continue;
        }
        let (left, right) = match exact_pair(context, *left, *right) {
            Ok(values) => values,
            Err(reason) => {
                result.add_abstention(context.abstention(
                    RuleKind::FieldComparison,
                    expression.span,
                    reason,
                ));
                continue;
            }
        };
        let signed = field.compare_signed(&left, &right);
        let unsigned = left.as_bigint().cmp(right.as_bigint());
        if comparison_result(*operator, signed) == comparison_result(*operator, unsigned) {
            continue;
        }
        result.add_finding(context.finding(
            RuleKind::FieldComparison,
            format!(
                concat!(
                    "Circom's signed field ordering and unsigned ordering disagree ",
                    "for exact operands {} and {}."
                ),
                left.as_bigint(),
                right.as_bigint()
            ),
            expression.span,
            "This comparison has different signed and unsigned results.".into(),
        ));
    }
    result
}

fn comparison_result(operator: BinaryOperator, order: Ordering) -> bool {
    if operator == BinaryOperator::Less {
        order == Ordering::Less
    } else if operator == BinaryOperator::Greater {
        order == Ordering::Greater
    } else if operator == BinaryOperator::LessEqual {
        order != Ordering::Greater
    } else {
        order != Ordering::Less
    }
}
