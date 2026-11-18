use std::collections::BTreeMap;
use std::fs;

use parser::hir::lift_project;
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_facts::relations::polynomial::query::EquationEvaluationError;
use crate::hir_facts::relations::polynomial::{Monomial, NormalizedEquation, QuadraticPolynomial};
use crate::hir_facts::{AccessKey, FieldContext, FieldValue};

fn keys() -> Vec<AccessKey> {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-equation-models-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, "template T(){signal input a;signal input b;signal input c;}").unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty());
    assert!(lifted.diagnostics.is_empty());
    let mut keys = Vec::new();
    for symbol in lifted.hir.symbols() {
        keys.push(AccessKey { root: symbol.id, instance: None, steps: Vec::new() });
    }
    assert_eq!(keys.len(), 3);
    keys
}

fn equation(field: &FieldContext, terms: &[(Monomial, i64)]) -> NormalizedEquation {
    let mut polynomial = QuadraticPolynomial::zero(field);
    for (monomial, coefficient) in terms {
        polynomial.add_term(field, monomial.clone(), field.canonical((*coefficient).into()));
    }
    NormalizedEquation::between(polynomial, QuadraticPolynomial::zero(field), field)
}

fn assignment(
    field: &FieldContext,
    keys: &[AccessKey],
    values: &[i64],
) -> BTreeMap<AccessKey, FieldValue> {
    keys.iter().cloned().zip(values.iter().map(|value| field.canonical((*value).into()))).collect()
}

#[test]
fn evaluates_constant_equations_without_assignments() {
    for curve in [Curve::Bn254, Curve::Bls12_381, Curve::Goldilocks] {
        let field = FieldContext::for_curve(curve);
        let values = BTreeMap::new();
        let zero = equation(&field, &[]);
        let one = equation(&field, &[(Monomial::Constant, -7)]);
        assert_eq!(zero.evaluate(&field, &values), Ok(field.canonical(0.into())));
        assert_eq!(one.evaluate(&field, &values), Ok(field.canonical(1.into())));
        assert!(zero.accesses().is_empty());
        assert!(one.accesses().is_empty());
        assert_eq!(zero.singleton_solution(&field), Ok(None));
        assert_eq!(one.singleton_solution(&field), Ok(None));
    }
}

#[test]
fn access_enumeration_is_sorted_unique_and_ignores_cancelled_terms() {
    let field = FieldContext::for_curve(Curve::Bn254);
    let keys = keys();
    let equation = equation(
        &field,
        &[
            (Monomial::Constant, 1),
            (Monomial::Quadratic(keys[0].clone(), keys[1].clone()), 2),
            (Monomial::Quadratic(keys[1].clone(), keys[1].clone()), 3),
            (Monomial::Linear(keys[0].clone()), 4),
            (Monomial::Linear(keys[2].clone()), 1),
            (Monomial::Linear(keys[2].clone()), -1),
        ],
    );
    assert_eq!(equation.accesses(), vec![&keys[0], &keys[1]]);
    assert_eq!(equation.singleton_solution(&field), Ok(None));
}

#[test]
fn evaluation_uses_both_quadratic_factors_and_signed_coefficients() {
    let keys = keys();
    for curve in [Curve::Bn254, Curve::Bls12_381, Curve::Goldilocks] {
        let field = FieldContext::for_curve(curve);
        let equation = equation(
            &field,
            &[
                (Monomial::Constant, 1),
                (Monomial::Linear(keys[0].clone()), -3),
                (Monomial::Quadratic(keys[0].clone(), keys[1].clone()), 2),
                (Monomial::Quadratic(keys[1].clone(), keys[1].clone()), -1),
            ],
        );
        let values = assignment(&field, &keys, &[2, 5, 0]);
        assert_eq!(equation.evaluate(&field, &values), Ok(field.canonical((-10).into())));
    }
}

#[test]
fn exhaustive_small_values_match_direct_field_arithmetic() {
    let keys = keys();
    for curve in [Curve::Bn254, Curve::Bls12_381, Curve::Goldilocks] {
        let field = FieldContext::for_curve(curve);
        for linear in -2..=2 {
            for quadratic in -2..=2 {
                let equation = equation(
                    &field,
                    &[
                        (Monomial::Constant, 1),
                        (Monomial::Linear(keys[0].clone()), linear),
                        (Monomial::Quadratic(keys[0].clone(), keys[1].clone()), quadratic),
                    ],
                );
                for left in -2..=2 {
                    for right in -2..=2 {
                        let values = assignment(&field, &keys, &[left, right, 0]);
                        let expected = 1 + linear * left + quadratic * left * right;
                        assert_eq!(
                            equation.evaluate(&field, &values),
                            Ok(field.canonical(expected.into()))
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn zero_value_never_exempts_a_missing_quadratic_operand() {
    let field = FieldContext::for_curve(Curve::Bn254);
    let keys = keys();
    let equation = equation(&field, &[(Monomial::Quadratic(keys[0].clone(), keys[1].clone()), 1)]);
    let mut values = assignment(&field, &keys[..1], &[0]);
    assert_eq!(
        equation.evaluate(&field, &values),
        Err(EquationEvaluationError::MissingValue(keys[1].clone()))
    );
    values.insert(keys[1].clone(), field.canonical(3.into()));
    assert_eq!(equation.evaluate(&field, &values), Ok(field.canonical(0.into())));
}

#[test]
fn missing_linear_operand_is_not_a_zero_default() {
    let field = FieldContext::for_curve(Curve::Bn254);
    let key = keys().remove(0);
    let equation = equation(&field, &[(Monomial::Linear(key.clone()), 1)]);
    assert_eq!(
        equation.evaluate(&field, &BTreeMap::new()),
        Err(EquationEvaluationError::MissingValue(key))
    );
}

#[test]
fn equation_queries_reject_a_different_field_even_without_variables() {
    let selected = FieldContext::for_curve(Curve::Bn254);
    let other = FieldContext::for_curve(Curve::Goldilocks);
    for equation in [equation(&selected, &[]), equation(&selected, &[(Monomial::Constant, 1)])] {
        assert_eq!(
            equation.evaluate(&other, &BTreeMap::new()),
            Err(EquationEvaluationError::WrongCurve)
        );
        assert_eq!(equation.singleton_solution(&other), Err(EquationEvaluationError::WrongCurve));
    }
}

#[test]
fn values_canonical_only_in_another_field_are_rejected() {
    let selected = FieldContext::for_curve(Curve::Goldilocks);
    let larger = FieldContext::for_curve(Curve::Bn254);
    let key = keys().remove(0);
    let equation = equation(&selected, &[(Monomial::Linear(key.clone()), 1)]);
    let values = BTreeMap::from([(key.clone(), larger.canonical(selected.modulus().clone()))]);
    assert_eq!(
        equation.evaluate(&selected, &values),
        Err(EquationEvaluationError::NoncanonicalValue(key))
    );
}

#[test]
fn singleton_solution_checks_scaled_reversed_and_zero_equalities() {
    let key = keys().remove(0);
    for curve in [Curve::Bn254, Curve::Bls12_381, Curve::Goldilocks] {
        let field = FieldContext::for_curve(curve);
        for (coefficient, constant, expected) in [(2, 6, -3), (-2, -6, -3), (3, 0, 0)] {
            let equation = equation(
                &field,
                &[(Monomial::Linear(key.clone()), coefficient), (Monomial::Constant, constant)],
            );
            let value = field.canonical(expected.into());
            assert_eq!(equation.singleton_solution(&field), Ok(Some((key.clone(), value.clone()))));
            let values = BTreeMap::from([(key.clone(), value)]);
            assert_eq!(equation.evaluate(&field, &values), Ok(field.canonical(0.into())));
        }
    }
}

#[test]
fn quadratic_and_multivariable_relations_never_provide_singleton_seeds() {
    let field = FieldContext::for_curve(Curve::Bn254);
    let keys = keys();
    for terms in [
        vec![(Monomial::Linear(keys[0].clone()), 1), (Monomial::Linear(keys[1].clone()), -1)],
        vec![(Monomial::Quadratic(keys[0].clone(), keys[0].clone()), 1)],
        vec![(Monomial::Quadratic(keys[0].clone(), keys[1].clone()), 1)],
    ] {
        assert_eq!(equation(&field, &terms).singleton_solution(&field), Ok(None));
    }
}

#[test]
fn selected_modulus_defines_the_canonical_integer_boundary() {
    for curve in [Curve::Bn254, Curve::Bls12_381, Curve::Goldilocks] {
        let field = FieldContext::for_curve(curve);
        assert_eq!(field.canonical(field.modulus().clone()), field.canonical(0.into()));
        assert_eq!(field.canonical(field.modulus() - 1).as_bigint(), &(field.modulus() - 1));
        assert_eq!(field.canonical((-1).into()).as_bigint(), &(field.modulus() - 1));
    }
}

#[test]
fn linear_target_completion_reuses_all_other_candidate_values() {
    let keys = keys();
    for curve in [Curve::Bn254, Curve::Bls12_381, Curve::Goldilocks] {
        let field = FieldContext::for_curve(curve);
        let relation = equation(
            &field,
            &[
                (Monomial::Linear(keys[0].clone()), 2),
                (Monomial::Quadratic(keys[1].clone(), keys[2].clone()), -2),
                (Monomial::Constant, -6),
            ],
        );
        let values = assignment(&field, &keys[1..], &[4, 5]);
        assert_eq!(
            relation.solve_linear_target(&field, &values, &keys[0]),
            Ok(Some(field.canonical(23.into())))
        );
        assert_eq!(relation.solve_linear_target(&field, &values, &keys[1]), Ok(None));
        let incomplete = assignment(&field, &keys[1..2], &[0]);
        assert_eq!(
            relation.solve_linear_target(&field, &incomplete, &keys[0]),
            Err(EquationEvaluationError::MissingValue(keys[2].clone()))
        );
    }
}

#[test]
fn target_completion_rejects_missing_or_quadratic_targets_and_wrong_fields() {
    let keys = keys();
    let field = FieldContext::for_curve(Curve::Goldilocks);
    let values = assignment(&field, &keys, &[0, 0, 0]);
    for monomial in [
        Monomial::Constant,
        Monomial::Quadratic(keys[0].clone(), keys[0].clone()),
        Monomial::Quadratic(keys[0].clone(), keys[1].clone()),
    ] {
        let relation = equation(&field, &[(monomial, 1)]);
        assert_eq!(relation.solve_linear_target(&field, &values, &keys[0]), Ok(None));
        assert_eq!(
            relation.solve_linear_target(&FieldContext::for_curve(Curve::Bn254), &values, &keys[0]),
            Err(EquationEvaluationError::WrongCurve)
        );
    }
}

#[test]
fn linear_pattern_matching_preserves_field_scale_coefficients_and_support() {
    let keys = keys();
    for curve in [Curve::Bn254, Curve::Bls12_381, Curve::Goldilocks] {
        let field = FieldContext::for_curve(curve);
        let normalized = equation(
            &field,
            &[
                (Monomial::Constant, -512),
                (Monomial::Linear(keys[0].clone()), 2),
                (Monomial::Linear(keys[1].clone()), -2),
                (Monomial::Linear(keys[2].clone()), 2),
            ],
        );
        let terms = [(keys[0].clone(), 1), (keys[1].clone(), -1), (keys[2].clone(), 1)];
        assert_eq!(normalized.matches_linear_relation(&field, (-256).into(), &terms), Ok(true));
        assert_eq!(normalized.matches_linear_relation(&field, (-255).into(), &terms), Ok(false));
        assert_eq!(
            normalized.matches_linear_relation(&field, (-256).into(), &terms[..2]),
            Ok(false)
        );
        let negated = [(keys[2].clone(), -1), (keys[1].clone(), 1), (keys[0].clone(), -1)];
        assert_eq!(normalized.matches_linear_relation(&field, 256.into(), &negated), Ok(true));
        let quadratic =
            equation(&field, &[(Monomial::Quadratic(keys[0].clone(), keys[1].clone()), 1)]);
        assert_eq!(quadratic.matches_linear_relation(&field, 0.into(), &terms), Ok(false));
    }
    let bn = FieldContext::for_curve(Curve::Bn254);
    let gold = FieldContext::for_curve(Curve::Goldilocks);
    assert_eq!(
        equation(&bn, &[]).matches_linear_relation(&gold, 0.into(), &[]),
        Err(EquationEvaluationError::WrongCurve)
    );
}
