//! Canonical quadratic expressions independent of source execution scope.

use std::collections::BTreeMap;

use parser::hir::{AccessPath, ExprId, ExprKind, HirProject, SymbolId, SymbolKind};
use parser::new_frontend::{BinaryOperator, UnaryOperator};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::access::{key_for_path, AccessKey};
use crate::hir_facts::field::{FieldContext, FieldValue};
use crate::hir_facts::forward::eval_expression_with_calls;
use crate::scalar_evidence::ScalarExpressionEvidence;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum CurveTag {
    Bn254,
    Bls12_381,
    Goldilocks,
}

impl From<&Curve> for CurveTag {
    fn from(curve: &Curve) -> Self {
        match curve {
            Curve::Bn254 => Self::Bn254,
            Curve::Bls12_381 => Self::Bls12_381,
            Curve::Goldilocks => Self::Goldilocks,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Monomial {
    Constant,
    Linear(AccessKey),
    Quadratic(AccessKey, AccessKey),
}

impl Monomial {
    fn multiply(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Self::Constant, term) | (term, Self::Constant) => Some(term.clone()),
            (Self::Linear(left), Self::Linear(right)) if left <= right => {
                Some(Self::Quadratic(left.clone(), right.clone()))
            }
            (Self::Linear(left), Self::Linear(right)) => {
                Some(Self::Quadratic(right.clone(), left.clone()))
            }
            (Self::Linear(_) | Self::Quadratic(_, _), Self::Quadratic(_, _))
            | (Self::Quadratic(_, _), Self::Linear(_)) => None,
        }
    }
}

/// Field-bound polynomial with canonical degree-zero, one, and two terms.
/// Its coefficients and curve cannot be supplied by warning consumers.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct QuadraticPolynomial {
    curve: CurveTag,
    terms: BTreeMap<Monomial, FieldValue>,
}

impl QuadraticPolynomial {
    pub(super) fn zero(field: &FieldContext) -> Self {
        Self { curve: CurveTag::from(field.curve()), terms: BTreeMap::new() }
    }

    pub(super) fn constant(field: &FieldContext, value: FieldValue) -> Self {
        let mut polynomial = Self::zero(field);
        polynomial.add_term(field, Monomial::Constant, value);
        polynomial
    }

    fn access(field: &FieldContext, key: AccessKey) -> Self {
        let mut polynomial = Self::zero(field);
        polynomial.add_term(field, Monomial::Linear(key), field.canonical(1.into()));
        polynomial
    }

    fn add_term(&mut self, field: &FieldContext, term: Monomial, value: FieldValue) {
        let value = if let Some(current) = self.terms.remove(&term) {
            field.add(&current, &value)
        } else {
            value
        };
        if !field.is_zero(&value) {
            self.terms.insert(term, value);
        }
    }

    fn add(&mut self, field: &FieldContext, other: Self) {
        for (term, value) in other.terms {
            self.add_term(field, term, value);
        }
    }

    fn scale(&mut self, field: &FieldContext, factor: &FieldValue) {
        for value in self.terms.values_mut() {
            *value = field.multiply(value, factor);
        }
        self.terms.retain(|_, value| !field.is_zero(value));
    }

    fn multiply(
        &self,
        field: &FieldContext,
        other: &Self,
        expression: ExprId,
    ) -> Result<Self, RelationBlocker> {
        let mut result = Self::zero(field);
        for (left, left_value) in &self.terms {
            for (right, right_value) in &other.terms {
                let term =
                    left.multiply(right).ok_or(RelationBlocker::DegreeExceeded(expression))?;
                result.add_term(field, term, field.multiply(left_value, right_value));
            }
        }
        Ok(result)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceForm {
    Constant,
    Linear,
    Quadratic,
    Unsupported,
}

impl SourceForm {
    fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::Constant, Self::Constant) => Self::Constant,
            (Self::Constant, Self::Linear)
            | (Self::Linear, Self::Constant)
            | (Self::Linear, Self::Linear) => Self::Linear,
            (Self::Constant | Self::Linear, Self::Quadratic)
            | (Self::Quadratic, Self::Constant | Self::Linear) => Self::Quadratic,
            (Self::Quadratic, Self::Quadratic)
            | (
                Self::Unsupported,
                Self::Constant | Self::Linear | Self::Quadratic | Self::Unsupported,
            )
            | (Self::Constant | Self::Linear | Self::Quadratic, Self::Unsupported) => {
                Self::Unsupported
            }
        }
    }

    fn multiply(self, other: Self) -> Self {
        match (self, other) {
            (Self::Constant, Self::Constant) => Self::Constant,
            (Self::Constant, Self::Linear) | (Self::Linear, Self::Constant) => Self::Linear,
            (Self::Constant, Self::Quadratic)
            | (Self::Quadratic, Self::Constant)
            | (Self::Linear, Self::Linear) => Self::Quadratic,
            (Self::Linear | Self::Quadratic, Self::Quadratic)
            | (Self::Quadratic, Self::Linear)
            | (
                Self::Unsupported,
                Self::Constant | Self::Linear | Self::Quadratic | Self::Unsupported,
            )
            | (Self::Constant | Self::Linear | Self::Quadratic, Self::Unsupported) => {
                Self::Unsupported
            }
        }
    }
}

struct ExpressionPolynomial {
    polynomial: QuadraticPolynomial,
    form: SourceForm,
}

impl ExpressionPolynomial {
    fn new(polynomial: QuadraticPolynomial, form: SourceForm) -> Self {
        Self { polynomial, form }
    }
}

/// An equation with all terms moved to zero and the first nonzero coefficient set to one.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct NormalizedEquation(QuadraticPolynomial);

impl NormalizedEquation {
    pub(super) fn between(
        mut left: QuadraticPolynomial,
        mut right: QuadraticPolynomial,
        field: &FieldContext,
    ) -> Self {
        right.scale(field, &field.canonical((-1).into()));
        left.add(field, right);
        if let Some((_, leading)) = left.terms.first_key_value() {
            if let Some(inverse) = field.inverse(leading) {
                left.scale(field, &inverse);
            }
        }
        Self(left)
    }
}

/// Why one generated constraint could not be normalized into a quadratic equation.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(crate) enum RelationBlocker {
    MissingExpression(ExprId),
    UnsupportedExpression(ExprId),
    UnsupportedPath,
    MissingRight,
    DegreeExceeded(ExprId),
    DepthExceeded(ExprId),
    GeneratedShape(ExprId),
}

pub(crate) struct NormalizationInputs<'a> {
    hir: &'a HirProject,
    field: &'a FieldContext,
    values: &'a BTreeMap<SymbolId, FieldValue>,
    calls: Option<&'a ScalarExpressionEvidence>,
}

impl<'a> NormalizationInputs<'a> {
    pub(crate) fn new(
        hir: &'a HirProject,
        field: &'a FieldContext,
        values: &'a BTreeMap<SymbolId, FieldValue>,
        calls: Option<&'a ScalarExpressionEvidence>,
    ) -> Self {
        Self { hir, field, values, calls }
    }
}

fn polynomial_for_path(
    inputs: &NormalizationInputs<'_>,
    path: &AccessPath,
) -> Result<QuadraticPolynomial, RelationBlocker> {
    let symbol = inputs.hir.symbol(path.terminal).ok_or(RelationBlocker::UnsupportedPath)?;
    if symbol.kind != SymbolKind::Signal {
        return Err(RelationBlocker::UnsupportedPath);
    }
    let key = key_for_path(inputs.hir, inputs.field, path, inputs.values);
    if !key.exact_alias(&key) {
        return Err(RelationBlocker::UnsupportedPath);
    }
    Ok(QuadraticPolynomial::access(inputs.field, key))
}

fn polynomial_for_expression(
    inputs: &NormalizationInputs<'_>,
    expression: ExprId,
    depth: usize,
) -> Result<ExpressionPolynomial, RelationBlocker> {
    if depth > 128 {
        return Err(RelationBlocker::DepthExceeded(expression));
    }
    if let Some(value) = eval_expression_with_calls(
        inputs.hir,
        inputs.field,
        expression,
        inputs.values,
        inputs.calls,
    ) {
        return Ok(ExpressionPolynomial::new(
            QuadraticPolynomial::constant(inputs.field, value),
            SourceForm::Constant,
        ));
    }
    let expr =
        inputs.hir.expression(expression).ok_or(RelationBlocker::MissingExpression(expression))?;
    match &expr.kind {
        ExprKind::Access(path) => polynomial_for_path(inputs, path)
            .map(|polynomial| ExpressionPolynomial::new(polynomial, SourceForm::Linear)),
        ExprKind::Parallel(inner) => polynomial_for_expression(inputs, *inner, depth + 1),
        ExprKind::Unary { operator: UnaryOperator::Negate, operand } => {
            let mut polynomial = polynomial_for_expression(inputs, *operand, depth + 1)?;
            polynomial.polynomial.scale(inputs.field, &inputs.field.canonical((-1).into()));
            Ok(polynomial)
        }
        ExprKind::Binary { operator, left, right } => {
            polynomial_for_binary(inputs, expression, *operator, (*left, *right), depth)
        }
        ExprKind::Number(_)
        | ExprKind::Unary { .. }
        | ExprKind::Ternary { .. }
        | ExprKind::Call { .. }
        | ExprKind::AnonymousComponent { .. }
        | ExprKind::Array(_)
        | ExprKind::Tuple(_)
        | ExprKind::Opaque(_) => Err(RelationBlocker::UnsupportedExpression(expression)),
    }
}

fn polynomial_for_binary(
    inputs: &NormalizationInputs<'_>,
    expression: ExprId,
    operator: BinaryOperator,
    operands: (ExprId, ExprId),
    depth: usize,
) -> Result<ExpressionPolynomial, RelationBlocker> {
    if operator != BinaryOperator::Add
        && operator != BinaryOperator::Subtract
        && operator != BinaryOperator::Multiply
    {
        return Err(RelationBlocker::UnsupportedExpression(expression));
    }
    let mut left = polynomial_for_expression(inputs, operands.0, depth + 1)?;
    let mut right = polynomial_for_expression(inputs, operands.1, depth + 1)?;
    if operator == BinaryOperator::Multiply {
        let form = left.form.multiply(right.form);
        let polynomial = left.polynomial.multiply(inputs.field, &right.polynomial, expression)?;
        return Ok(ExpressionPolynomial { polynomial, form });
    }
    if operator == BinaryOperator::Subtract {
        right.polynomial.scale(inputs.field, &inputs.field.canonical((-1).into()));
    }
    left.polynomial.add(inputs.field, right.polynomial);
    left.form = left.form.add(right.form);
    Ok(left)
}

pub(crate) fn constraint_equation(
    inputs: &NormalizationInputs<'_>,
    kind: &CfgNodeKind,
) -> Result<NormalizedEquation, RelationBlocker> {
    let CfgNodeKind::Constraint { target, left, right } = kind else {
        return Err(RelationBlocker::UnsupportedPath);
    };
    let left_side = if let Some(target) = target {
        ExpressionPolynomial::new(polynomial_for_path(inputs, target)?, SourceForm::Linear)
    } else {
        polynomial_for_expression(inputs, *left, 0)?
    };
    let right_side = if target.is_some() {
        polynomial_for_expression(inputs, *left, 0)?
    } else {
        let right = right.ok_or(RelationBlocker::MissingRight)?;
        polynomial_for_expression(inputs, right, 0)?
    };
    if left_side.form.add(right_side.form) == SourceForm::Unsupported {
        return Err(RelationBlocker::GeneratedShape(*left));
    }
    Ok(NormalizedEquation::between(left_side.polynomial, right_side.polynomial, inputs.field))
}

pub(super) fn witness_equation(
    inputs: &NormalizationInputs<'_>,
    target: &AccessPath,
    value: ExprId,
) -> Result<NormalizedEquation, RelationBlocker> {
    let target = polynomial_for_path(inputs, target)?;
    let value = polynomial_for_expression(inputs, value, 0)?;
    Ok(NormalizedEquation::between(target, value.polynomial, inputs.field))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use std::fs;

    use abstract_interpretation::graph::FlowGraph;
    use parser::hir::lift_project;
    use parser::new_frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::{build_cfg, CfgNodeKind};
    use crate::hir_facts::field::FieldContext;
    use crate::hir_facts::relations::polynomial::{
        constraint_equation, witness_equation, NormalizationInputs,
    };

    #[test]
    fn generated_assignment_polynomials_can_match_without_an_execution_certificate() {
        let source = "template T(){signal input a;signal input b;signal output x;\
                      x<--a*b;x<==b*a;}";
        let directory = std::env::temp_dir().join(format!(
            "circomspect-polynomial-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("case.circom");
        fs::write(&path, source).unwrap();
        let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        assert!(lifted.syntax_diagnostics.is_empty());
        assert!(lifted.diagnostics.is_empty());
        let cfg = build_cfg(&lifted.hir, lifted.hir.definition("T").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let values = BTreeMap::new();
        let inputs = NormalizationInputs::new(&lifted.hir, &field, &values, None);
        let mut witness = None;
        let mut generated = None;
        for site in cfg.nodes() {
            let node = cfg.node(*site).unwrap();
            if let CfgNodeKind::Witness { target, value } = &node.kind {
                if witness.is_none() {
                    witness = Some(witness_equation(&inputs, target, *value).unwrap());
                }
            }
            if let CfgNodeKind::Constraint { target: Some(_), .. } = &node.kind {
                generated = Some(constraint_equation(&inputs, &node.kind).unwrap());
            }
        }
        assert_eq!(witness.unwrap(), generated.unwrap());
    }
}
