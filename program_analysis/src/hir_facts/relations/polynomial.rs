//! Canonical quadratic expressions independent of source execution scope.

mod query;

use std::collections::BTreeMap;

use abstract_interpretation::lattice::Lattice;
use parser::hir::{AccessPath, ExprId, ExprKind, HirProject, SymbolId, SymbolKind};
use parser::new_frontend::{BinaryOperator, UnaryOperator};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::{CfgNodeKind, Constraint};
use crate::hir_facts::access::{key_for_path, AccessKey};
use crate::hir_facts::field::{FieldContext, FieldValue};
use crate::hir_facts::forward::eval_expression_with_calls;
use crate::hir_facts::VisitAccesses;
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
            (Self::Constant | Self::Linear, Self::Linear) | (Self::Linear, Self::Constant) => {
                Self::Linear
            }
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExpressionPolynomial {
    polynomial: QuadraticPolynomial,
    form: SourceForm,
}

impl ExpressionPolynomial {
    fn new(polynomial: QuadraticPolynomial, form: SourceForm) -> Self {
        Self { polynomial, form }
    }

    pub(crate) fn constant(field: &FieldContext, value: FieldValue) -> Self {
        Self::new(QuadraticPolynomial::constant(field, value), SourceForm::Constant)
    }

    pub(crate) fn add(&mut self, field: &FieldContext, other: Self) {
        self.polynomial.add(field, other.polynomial);
        self.form = self.form.add(other.form);
    }

    fn certifies_exact_scalar(&self, field: &FieldContext, value: &FieldValue) -> bool {
        self.form == SourceForm::Constant
            && self.polynomial == QuadraticPolynomial::constant(field, value.clone())
    }
}

/// Must-defined scalar variables with both canonical value and source shape.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MustSymbolicVariables {
    Unreachable,
    Reached(BTreeMap<SymbolId, ExpressionPolynomial>),
}

impl MustSymbolicVariables {
    pub(crate) fn reachable_empty() -> Self {
        Self::Reached(BTreeMap::new())
    }

    pub(crate) fn get(&self, symbol: SymbolId) -> Option<&ExpressionPolynomial> {
        let Self::Reached(values) = self else { return None };
        values.get(&symbol)
    }

    pub(crate) fn insert(&mut self, symbol: SymbolId, value: ExpressionPolynomial) {
        if let Self::Reached(values) = self {
            values.insert(symbol, value);
        }
    }

    pub(crate) fn remove(&mut self, symbol: SymbolId) {
        if let Self::Reached(values) = self {
            values.remove(&symbol);
        }
    }
}

impl Lattice for MustSymbolicVariables {
    fn bottom() -> Self {
        Self::Unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unreachable, _) => true,
            (Self::Reached(_), Self::Unreachable) => false,
            (Self::Reached(left), Self::Reached(right)) => {
                right.iter().all(|(symbol, value)| left.get(symbol) == Some(value))
            }
        }
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        let Self::Reached(right) = other else { return false };
        let Self::Reached(left) = self else {
            *self = other.clone();
            return true;
        };
        let old = left.clone();
        left.retain(|symbol, value| right.get(symbol) == Some(value));
        *left != old
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
    DegreeExceeded(ExprId),
    GeneratedShape(ExprId),
}

pub(crate) struct NormalizationInputs<'a> {
    hir: &'a HirProject,
    field: &'a FieldContext,
    values: &'a BTreeMap<SymbolId, FieldValue>,
    calls: Option<&'a ScalarExpressionEvidence>,
    symbolic: &'a MustSymbolicVariables,
}

impl<'a> NormalizationInputs<'a> {
    pub(crate) fn new(
        hir: &'a HirProject,
        field: &'a FieldContext,
        values: &'a BTreeMap<SymbolId, FieldValue>,
        calls: Option<&'a ScalarExpressionEvidence>,
        symbolic: &'a MustSymbolicVariables,
    ) -> Self {
        Self { hir, field, values, calls, symbolic }
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

enum ExpressionFrame {
    Evaluate(ExprId),
    Negate(ExprId),
    Binary { expression: ExprId, operator: BinaryOperator },
}

fn polynomial_for_expression(
    inputs: &NormalizationInputs<'_>,
    expression: ExprId,
) -> Result<ExpressionPolynomial, RelationBlocker> {
    let mut frames = vec![ExpressionFrame::Evaluate(expression)];
    let mut values = Vec::new();
    while let Some(frame) = frames.pop() {
        match frame {
            ExpressionFrame::Evaluate(expression) => {
                evaluate_expression_frame(inputs, expression, &mut frames, &mut values)?;
            }
            ExpressionFrame::Negate(expression) => {
                let Some(mut operand) = values.pop() else {
                    return Err(RelationBlocker::MissingExpression(expression));
                };
                operand.polynomial.scale(inputs.field, &inputs.field.canonical((-1).into()));
                values.push(operand);
            }
            ExpressionFrame::Binary { expression, operator } => {
                let Some(right) = values.pop() else {
                    return Err(RelationBlocker::MissingExpression(expression));
                };
                let Some(left) = values.pop() else {
                    return Err(RelationBlocker::MissingExpression(expression));
                };
                values.push(combine_binary(inputs, expression, operator, left, right)?);
            }
        }
    }
    values.pop().ok_or(RelationBlocker::MissingExpression(expression))
}

fn evaluate_expression_frame(
    inputs: &NormalizationInputs<'_>,
    expression: ExprId,
    frames: &mut Vec<ExpressionFrame>,
    values: &mut Vec<ExpressionPolynomial>,
) -> Result<(), RelationBlocker> {
    let expr =
        inputs.hir.expression(expression).ok_or(RelationBlocker::MissingExpression(expression))?;
    match &expr.kind {
        ExprKind::Access(path) => values.push(polynomial_for_access(inputs, path, expression)?),
        ExprKind::Parallel(inner) => frames.push(ExpressionFrame::Evaluate(*inner)),
        ExprKind::Unary { operator: UnaryOperator::Negate, operand } => {
            frames.push(ExpressionFrame::Negate(expression));
            frames.push(ExpressionFrame::Evaluate(*operand));
        }
        ExprKind::Binary { operator, left, right }
            if [BinaryOperator::Add, BinaryOperator::Subtract, BinaryOperator::Multiply]
                .contains(operator) =>
        {
            frames.push(ExpressionFrame::Binary { expression, operator: *operator });
            frames.push(ExpressionFrame::Evaluate(*right));
            frames.push(ExpressionFrame::Evaluate(*left));
        }
        ExprKind::Number(_)
        | ExprKind::Binary { .. }
        | ExprKind::Unary { .. }
        | ExprKind::Ternary { .. }
        | ExprKind::Call { .. }
        | ExprKind::AnonymousComponent { .. }
        | ExprKind::Array(_)
        | ExprKind::Tuple(_)
        | ExprKind::Opaque(_) => {
            let Some(checked_values) = checked_fallback_values(inputs, expression) else {
                return Err(RelationBlocker::UnsupportedExpression(expression));
            };
            let Some(value) = eval_expression_with_calls(
                inputs.hir,
                inputs.field,
                expression,
                &checked_values,
                inputs.calls,
            ) else {
                return Err(RelationBlocker::UnsupportedExpression(expression));
            };
            values.push(ExpressionPolynomial::constant(inputs.field, value));
        }
    }
    Ok(())
}

fn checked_fallback_values(
    inputs: &NormalizationInputs<'_>,
    expression: ExprId,
) -> Option<BTreeMap<SymbolId, FieldValue>> {
    let mut values = BTreeMap::new();
    let mut allowed = true;
    let complete = expression.visit_accesses_with(
        inputs.hir,
        &|call| inputs.calls.and_then(|calls| calls.call_value(call)).is_some(),
        &mut |path| {
            if let Some((symbol, value)) = foldable_access(inputs, path) {
                values.insert(symbol, value);
            } else {
                allowed = false;
            }
        },
    );
    (complete && allowed).then_some(values)
}

fn foldable_access(
    inputs: &NormalizationInputs<'_>,
    path: &AccessPath,
) -> Option<(SymbolId, FieldValue)> {
    if path.root != path.terminal || !path.steps.is_empty() {
        return None;
    }
    let symbol = inputs.hir.symbol(path.root)?;
    let value = inputs.values.get(&path.root)?;
    match symbol.kind {
        SymbolKind::Parameter => Some((path.root, value.clone())),
        SymbolKind::Variable
            if inputs
                .symbolic
                .get(path.root)
                .is_some_and(|symbolic| symbolic.certifies_exact_scalar(inputs.field, value)) =>
        {
            Some((path.root, value.clone()))
        }
        SymbolKind::Variable
        | SymbolKind::Signal
        | SymbolKind::Component
        | SymbolKind::Bus
        | SymbolKind::Tag => None,
    }
}

fn polynomial_for_access(
    inputs: &NormalizationInputs<'_>,
    path: &AccessPath,
    expression: ExprId,
) -> Result<ExpressionPolynomial, RelationBlocker> {
    let symbol = inputs.hir.symbol(path.root).ok_or(RelationBlocker::UnsupportedPath)?;
    if symbol.kind == SymbolKind::Variable && path.root == path.terminal && path.steps.is_empty() {
        return inputs
            .symbolic
            .get(path.root)
            .cloned()
            .ok_or(RelationBlocker::UnsupportedExpression(expression));
    }
    if let Some(value) = eval_expression_with_calls(
        inputs.hir,
        inputs.field,
        expression,
        inputs.values,
        inputs.calls,
    ) {
        return Ok(ExpressionPolynomial::constant(inputs.field, value));
    }
    Ok(ExpressionPolynomial::new(polynomial_for_path(inputs, path)?, SourceForm::Linear))
}

pub(crate) fn variable_polynomial(
    inputs: &NormalizationInputs<'_>,
    expression: ExprId,
) -> Result<ExpressionPolynomial, RelationBlocker> {
    polynomial_for_expression(inputs, expression)
}

fn combine_binary(
    inputs: &NormalizationInputs<'_>,
    expression: ExprId,
    operator: BinaryOperator,
    mut left: ExpressionPolynomial,
    mut right: ExpressionPolynomial,
) -> Result<ExpressionPolynomial, RelationBlocker> {
    if operator != BinaryOperator::Add
        && operator != BinaryOperator::Subtract
        && operator != BinaryOperator::Multiply
    {
        return Err(RelationBlocker::UnsupportedExpression(expression));
    }
    if operator == BinaryOperator::Multiply {
        let form = left.form.multiply(right.form);
        let polynomial = left.polynomial.multiply(inputs.field, &right.polynomial, expression)?;
        return Ok(ExpressionPolynomial { polynomial, form });
    }
    if operator == BinaryOperator::Subtract {
        right.polynomial.scale(inputs.field, &inputs.field.canonical((-1).into()));
    }
    left.add(inputs.field, right);
    Ok(left)
}

pub(crate) fn constraint_equation(
    inputs: &NormalizationInputs<'_>,
    kind: &CfgNodeKind,
) -> Result<NormalizedEquation, RelationBlocker> {
    let CfgNodeKind::Constraint(constraint) = kind else {
        return Err(RelationBlocker::UnsupportedPath);
    };
    let (left_side, right_side, source) = match constraint {
        Constraint::Assignment { target, value } => (
            ExpressionPolynomial::new(polynomial_for_path(inputs, target)?, SourceForm::Linear),
            polynomial_for_expression(inputs, *value)?,
            *value,
        ),
        Constraint::Equality { left, right } => (
            polynomial_for_expression(inputs, *left)?,
            polynomial_for_expression(inputs, *right)?,
            *left,
        ),
    };
    if left_side.form.add(right_side.form) == SourceForm::Unsupported {
        return Err(RelationBlocker::GeneratedShape(source));
    }
    Ok(NormalizedEquation::between(left_side.polynomial, right_side.polynomial, inputs.field))
}

pub(super) fn witness_equation(
    inputs: &NormalizationInputs<'_>,
    target: &AccessPath,
    value: ExprId,
) -> Result<NormalizedEquation, RelationBlocker> {
    let target = polynomial_for_path(inputs, target)?;
    let value = polynomial_for_expression(inputs, value)?;
    Ok(NormalizedEquation::between(target, value.polynomial, inputs.field))
}

pub(super) fn boolean_equation(field: &FieldContext, bit: &AccessKey) -> NormalizedEquation {
    let mut polynomial = QuadraticPolynomial::zero(field);
    polynomial.add_term(
        field,
        Monomial::Quadratic(bit.clone(), bit.clone()),
        field.canonical(1.into()),
    );
    polynomial.add_term(field, Monomial::Linear(bit.clone()), field.canonical((-1).into()));
    NormalizedEquation::between(polynomial, QuadraticPolynomial::zero(field), field)
}

pub(super) fn reconstruction_equation(
    field: &FieldContext,
    input: &AccessKey,
    bits: &[AccessKey],
) -> NormalizedEquation {
    let input = QuadraticPolynomial::access(field, input.clone());
    let mut sum = QuadraticPolynomial::zero(field);
    let mut weight = field.canonical(1.into());
    for bit in bits {
        let mut term = QuadraticPolynomial::access(field, bit.clone());
        term.scale(field, &weight);
        sum.add(field, term);
        weight = field.add(&weight, &weight);
    }
    NormalizedEquation::between(input, sum, field)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};
    use std::fs;

    use abstract_interpretation::graph::FlowGraph;
    use parser::hir::{lift_project, ExprId, ExprKind, HirProject, SymbolId};
    use parser::new_frontend::{load_sources, BinaryOperator, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::{Constraint, build_cfg, CfgNodeKind};
    use crate::hir_facts::field::FieldContext;
    use crate::hir_facts::relations::polynomial::{
        constraint_equation, variable_polynomial, witness_equation, ExpressionPolynomial,
        MustSymbolicVariables, NormalizationInputs, QuadraticPolynomial, SourceForm,
    };
    use crate::scalar_evidence::ScalarExpressionEvidence;
    use abstract_interpretation::lattice::Lattice;

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
        let symbolic = MustSymbolicVariables::reachable_empty();
        let inputs = NormalizationInputs::new(&lifted.hir, &field, &values, None, &symbolic);
        let mut witness = None;
        let mut generated = None;
        for site in cfg.nodes() {
            let node = cfg.node(*site).unwrap();
            if let CfgNodeKind::Witness { target, value } = &node.kind {
                if witness.is_none() {
                    witness = Some(witness_equation(&inputs, target, *value).unwrap());
                }
            }
            if let CfgNodeKind::Constraint(Constraint::Assignment { .. }) = &node.kind {
                generated = Some(constraint_equation(&inputs, &node.kind).unwrap());
            }
        }
        assert_eq!(witness.unwrap(), generated.unwrap());
    }

    #[test]
    fn symbolic_variable_join_preserves_source_shape_and_lattice_laws() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-symbolic-lattice-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("case.circom");
        fs::write(&path, "function F(){var x=0;var y=0;}").unwrap();
        let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let x = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap().id;
        let y = hir.symbols().iter().find(|symbol| symbol.name == "y").unwrap().id;
        let field = FieldContext::for_curve(Curve::Bn254);
        let constant = ExpressionPolynomial::constant(&field, field.canonical(1.into()));
        let linear = ExpressionPolynomial::new(
            QuadraticPolynomial::constant(&field, field.canonical(1.into())),
            SourceForm::Linear,
        );
        assert_ne!(constant, linear);
        let states = [
            MustSymbolicVariables::Unreachable,
            MustSymbolicVariables::reachable_empty(),
            MustSymbolicVariables::Reached(BTreeMap::from([(x, constant.clone())])),
            MustSymbolicVariables::Reached(BTreeMap::from([(x, linear.clone())])),
            MustSymbolicVariables::Reached(BTreeMap::from([(y, constant.clone())])),
            MustSymbolicVariables::Reached(BTreeMap::from([(x, constant), (y, linear)])),
        ];
        for left in &states {
            let mut idempotent = left.clone();
            assert!(!idempotent.join_assign(left));
            for right in &states {
                let mut joined = left.clone();
                joined.join_assign(right);
                assert!(left.leq(&joined));
                assert!(right.leq(&joined));
                let mut reverse = right.clone();
                reverse.join_assign(left);
                assert_eq!(joined, reverse);
                for last in &states {
                    let mut first = joined.clone();
                    first.join_assign(last);
                    let mut second = right.clone();
                    second.join_assign(last);
                    let mut reassociated = left.clone();
                    reassociated.join_assign(&second);
                    assert_eq!(first, reassociated);
                }
            }
        }
    }

    fn assigned_expression(hir: &HirProject, name: &str) -> ExprId {
        let cfg = build_cfg(hir, hir.definition("T").unwrap()).unwrap();
        for site in cfg.nodes() {
            let Some(node) = cfg.node(*site) else { panic!("CFG site must exist") };
            let CfgNodeKind::Assignment { target, value, .. } = &node.kind else { continue };
            let Some(symbol) = hir.symbol(target.root) else { panic!("target must exist") };
            if symbol.name == name {
                return *value;
            }
        }
        panic!("assignment {name} must exist")
    }

    fn access_expression(hir: &HirProject, symbol: SymbolId) -> ExprId {
        for expression in hir.expressions() {
            let ExprKind::Access(path) = &expression.kind else { continue };
            if path.root == symbol {
                return expression.id;
            }
        }
        panic!("symbol access must exist")
    }

    fn parameter_comparison(hir: &HirProject, parameter: SymbolId) -> ExprId {
        for expression in hir.expressions() {
            let ExprKind::Binary { operator: BinaryOperator::Equal, left, .. } = &expression.kind
            else {
                continue;
            };
            let Some(left) = hir.expression(*left) else { continue };
            let ExprKind::Access(path) = &left.kind else { continue };
            if path.root == parameter {
                return expression.id;
            }
        }
        panic!("parameter comparison must exist")
    }

    #[test]
    fn lost_variable_shape_cannot_borrow_an_exact_parameter_value() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-symbolic-parameter-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("case.circom");
        fs::write(
            &path,
            "template T(n){signal input a;var x=a-a+1;var y=x+n;\
             var wrapped=x==1;var negated=!x;var parameter=n==2;}",
        )
        .unwrap();
        let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let x = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap().id;
        let n = hir.symbols().iter().find(|symbol| symbol.name == "n").unwrap().id;
        let x_access = access_expression(&hir, x);
        let n_access = access_expression(&hir, n);
        let wrapped = assigned_expression(&hir, "wrapped");
        let negated = assigned_expression(&hir, "negated");
        let wrapped_parameter = parameter_comparison(&hir, n);
        let field = FieldContext::for_curve(Curve::Bn254);
        let one = field.canonical(1.into());
        let two = field.canonical(2.into());
        let values = BTreeMap::from([(x, one.clone()), (n, two.clone())]);
        let empty = MustSymbolicVariables::reachable_empty();
        let inputs = NormalizationInputs::new(&hir, &field, &values, None, &empty);
        assert!(variable_polynomial(&inputs, x_access).is_err());
        assert!(variable_polynomial(&inputs, wrapped).is_err());
        assert!(variable_polynomial(&inputs, negated).is_err());
        assert_eq!(
            variable_polynomial(&inputs, wrapped_parameter).unwrap(),
            ExpressionPolynomial::constant(&field, field.canonical(1.into()))
        );
        assert_eq!(
            variable_polynomial(&inputs, n_access).unwrap(),
            ExpressionPolynomial::constant(&field, two)
        );
        let unknown = BTreeMap::from([(x, one.clone())]);
        let inputs = NormalizationInputs::new(&hir, &field, &unknown, None, &empty);
        assert!(variable_polynomial(&inputs, n_access).is_err());
        let mut symbolic = empty;
        symbolic.insert(x, ExpressionPolynomial::constant(&field, one.clone()));
        let inputs = NormalizationInputs::new(&hir, &field, &values, None, &symbolic);
        assert_eq!(
            variable_polynomial(&inputs, wrapped).unwrap(),
            ExpressionPolynomial::constant(&field, field.canonical(1.into()))
        );
        let linear = ExpressionPolynomial::new(
            QuadraticPolynomial::constant(&field, one),
            SourceForm::Linear,
        );
        symbolic.insert(x, linear.clone());
        let inputs = NormalizationInputs::new(&hir, &field, &values, None, &symbolic);
        assert_eq!(variable_polynomial(&inputs, x_access).unwrap(), linear);
        assert!(variable_polynomial(&inputs, wrapped).is_err());
    }

    #[test]
    fn exact_call_result_cannot_hide_signal_derived_argument_shape() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-symbolic-call-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("case.circom");
        fs::write(
            &path,
            "function F(v){return 1;}template T(){signal input a;var x=a-a+1;var y=F(x);}",
        )
        .unwrap();
        let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let provider =
            crate::interprocedural::ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let hir = &lifted.hir;
        let definition = hir.definition("T").unwrap();
        let x = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap().id;
        let call = hir
            .expressions()
            .iter()
            .find_map(|expression| {
                let ExprKind::Call { .. } = &expression.kind else { return None };
                Some(expression.id)
            })
            .unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let one = field.canonical(1.into());
        let values = BTreeMap::from([(x, one.clone())]);
        let context = provider.symbolic_context_for(definition).unwrap();
        let mut calls = ScalarExpressionEvidence::empty(hir, &context, Curve::Bn254);
        calls.insert_call(call, one.clone(), BTreeSet::new());
        let empty = MustSymbolicVariables::reachable_empty();
        let inputs = NormalizationInputs::new(hir, &field, &values, Some(&calls), &empty);
        assert!(variable_polynomial(&inputs, call).is_err());
        let mut symbolic = empty;
        symbolic.insert(
            x,
            ExpressionPolynomial::new(
                QuadraticPolynomial::constant(&field, one.clone()),
                SourceForm::Linear,
            ),
        );
        let inputs = NormalizationInputs::new(hir, &field, &values, Some(&calls), &symbolic);
        assert!(variable_polynomial(&inputs, call).is_err());
        symbolic.insert(x, ExpressionPolynomial::constant(&field, one.clone()));
        let inputs = NormalizationInputs::new(hir, &field, &values, Some(&calls), &symbolic);
        assert_eq!(
            variable_polynomial(&inputs, call).unwrap(),
            ExpressionPolynomial::constant(&field, one)
        );
    }
}
