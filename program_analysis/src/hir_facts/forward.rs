use std::collections::{BTreeMap, BTreeSet};
use std::cmp::Ordering;
use std::sync::Arc;

use abstract_interpretation::graph::NodeId;
use abstract_interpretation::lattice::Lattice;
use abstract_interpretation::solver::{DataflowAnalysis, Transfer, TransferOutcome};
use parser::hir::{AccessPath, CallTarget, ExprId, ExprKind, HirProject, SymbolId, SymbolKind};
use parser::new_frontend::{AssignmentOperator, BinaryOperator, PostfixOperator, UnaryOperator};

use crate::hir_cfg::{CfgEdge, CfgNode, CfgNodeKind, DefinitionCfg, EdgeKind};
use crate::scalar_evidence::ScalarExpressionEvidence;

use crate::hir_facts::access::{key_for_path, AccessKey, MayAccessSet};
use crate::hir_facts::domains::DegreeUpper;
use crate::hir_facts::field::{FieldContext, FieldValue, ShiftDirection};
use crate::hir_facts::relations::{
    constraint_equation, variable_polynomial, ExpressionPolynomial, MustEquations,
    MustSymbolicVariables, NormalizationInputs,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ForwardState {
    Unreachable,
    Reached {
        variables: BTreeMap<SymbolId, FieldValue>,
        symbolic: Arc<MustSymbolicVariables>,
        dependencies: BTreeMap<SymbolId, MayAccessSet>,
        degrees: BTreeMap<SymbolId, DegreeUpper>,
        may_constraints: BTreeSet<NodeId>,
        must_constraints: BTreeSet<NodeId>,
        must_touches: BTreeSet<AccessKey>,
        must_fixed: BTreeSet<(AccessKey, FieldValue)>,
        must_equations: Arc<MustEquations>,
    },
}

// The CFG fixes the finite set of constraint-site IDs. Each variable maps to
// one canonical value or unknown and can lose precision only once at a join.
// May-sites grow by union; must-sites shrink by intersection. Thus this
// product domain has finite height for each definition.

impl ForwardState {
    pub fn boundary() -> Self {
        Self::Reached {
            variables: BTreeMap::new(),
            symbolic: Arc::new(MustSymbolicVariables::reachable_empty()),
            dependencies: BTreeMap::new(),
            degrees: BTreeMap::new(),
            may_constraints: BTreeSet::new(),
            must_constraints: BTreeSet::new(),
            must_touches: BTreeSet::new(),
            must_fixed: BTreeSet::new(),
            must_equations: Arc::new(MustEquations::reachable_empty()),
        }
    }

    pub fn with_scalar_parameters(values: &BTreeMap<SymbolId, FieldValue>) -> Self {
        let mut state = Self::boundary();
        if let Self::Reached { variables, .. } = &mut state {
            variables.extend(values.iter().map(|(symbol, value)| (*symbol, value.clone())));
        }
        state
    }

    pub fn variables(&self) -> Option<&BTreeMap<SymbolId, FieldValue>> {
        let Self::Reached { variables, .. } = self else { return None };
        Some(variables)
    }

    pub(crate) fn symbolic(&self) -> Option<&MustSymbolicVariables> {
        let Self::Reached { symbolic, .. } = self else { return None };
        Some(symbolic)
    }

    pub fn dependencies(&self) -> Option<&BTreeMap<SymbolId, MayAccessSet>> {
        let Self::Reached { dependencies, .. } = self else { return None };
        Some(dependencies)
    }

    pub fn degrees(&self) -> Option<&BTreeMap<SymbolId, DegreeUpper>> {
        let Self::Reached { degrees, .. } = self else { return None };
        Some(degrees)
    }

    pub fn constraints(&self) -> Option<(&BTreeSet<NodeId>, &BTreeSet<NodeId>)> {
        let Self::Reached { may_constraints, must_constraints, .. } = self else { return None };
        Some((may_constraints, must_constraints))
    }

    pub fn fixed_equations(&self) -> Option<&BTreeSet<(AccessKey, FieldValue)>> {
        let Self::Reached { must_fixed, .. } = self else { return None };
        Some(must_fixed)
    }

    pub fn must_touches(&self) -> Option<&BTreeSet<AccessKey>> {
        let Self::Reached { must_touches, .. } = self else { return None };
        Some(must_touches)
    }

    pub(crate) fn must_equations(&self) -> &MustEquations {
        match self {
            Self::Unreachable => &MustEquations::Unreachable,
            Self::Reached { must_equations, .. } => must_equations,
        }
    }
}

impl Lattice for ForwardState {
    fn bottom() -> Self {
        Self::Unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unreachable, _) => true,
            (Self::Reached { .. }, Self::Unreachable) => false,
            (
                Self::Reached {
                    variables: left,
                    symbolic: left_symbolic,
                    dependencies: left_dependencies,
                    degrees: left_degrees,
                    may_constraints: left_may,
                    must_constraints: left_must,
                    must_touches: left_touches,
                    must_fixed: left_fixed,
                    must_equations: left_equations,
                },
                Self::Reached {
                    variables: right,
                    symbolic: right_symbolic,
                    dependencies: right_dependencies,
                    degrees: right_degrees,
                    may_constraints: right_may,
                    must_constraints: right_must,
                    must_touches: right_touches,
                    must_fixed: right_fixed,
                    must_equations: right_equations,
                },
            ) => {
                right.iter().all(|(key, value)| left.get(key) == Some(value))
                    && left_symbolic.leq(right_symbolic)
                    && right_dependencies.iter().all(|(key, right)| {
                        left_dependencies.get(key).is_some_and(|left| left.leq(right))
                    })
                    && right_degrees
                        .iter()
                        .all(|(key, right)| left_degrees.get(key).is_some_and(|left| left <= right))
                    && left_may.is_subset(right_may)
                    && left_must.is_superset(right_must)
                    && left_touches.is_superset(right_touches)
                    && left_fixed.is_superset(right_fixed)
                    && left_equations.leq(right_equations)
            }
        }
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        if let Self::Unreachable = other {
            return false;
        }
        if let Self::Unreachable = self {
            *self = other.clone();
            return true;
        }
        let old = self.clone();
        let (
            Self::Reached {
                variables: left,
                symbolic: left_symbolic,
                dependencies: left_dependencies,
                degrees: left_degrees,
                may_constraints: left_may,
                must_constraints: left_must,
                must_touches: left_touches,
                must_fixed: left_fixed,
                must_equations: left_equations,
            },
            Self::Reached {
                variables: right,
                symbolic: right_symbolic,
                dependencies: right_dependencies,
                degrees: right_degrees,
                may_constraints: right_may,
                must_constraints: right_must,
                must_touches: right_touches,
                must_fixed: right_fixed,
                must_equations: right_equations,
            },
        ) = (&mut *self, other)
        else {
            return false;
        };
        left.retain(|key, value| right.get(key) == Some(value));
        left_symbolic.join_assign(right_symbolic);
        left_dependencies.retain(|key, left| {
            let Some(right) = right_dependencies.get(key) else { return false };
            left.join_assign(right);
            true
        });
        left_degrees.retain(|key, left| {
            let Some(right) = right_degrees.get(key) else { return false };
            *left = (*left).max(*right);
            *left != DegreeUpper::Unbounded
        });
        left_may.extend(right_may);
        left_must.retain(|site| right_must.contains(site));
        left_touches.retain(|key| right_touches.contains(key));
        left_fixed.retain(|equation| right_fixed.contains(equation));
        left_equations.join_assign(right_equations);
        *self != old
    }
}

pub struct ForwardAnalysis<'a> {
    pub hir: &'a HirProject,
    pub field: &'a FieldContext,
    initial_values: BTreeMap<SymbolId, FieldValue>,
    calls: Option<&'a ScalarExpressionEvidence>,
}

impl<'a> ForwardAnalysis<'a> {
    pub fn new(hir: &'a HirProject, field: &'a FieldContext) -> Self {
        Self { hir, field, initial_values: BTreeMap::new(), calls: None }
    }

    pub fn with_scalar_parameters(
        hir: &'a HirProject,
        field: &'a FieldContext,
        values: BTreeMap<SymbolId, FieldValue>,
    ) -> Self {
        Self { hir, field, initial_values: values, calls: None }
    }

    pub(crate) fn with_scalar_parameters_and_calls(
        hir: &'a HirProject,
        field: &'a FieldContext,
        values: BTreeMap<SymbolId, FieldValue>,
        calls: Option<&'a ScalarExpressionEvidence>,
    ) -> Self {
        Self { hir, field, initial_values: values, calls }
    }

    pub(crate) fn with_call_values(
        hir: &'a HirProject,
        field: &'a FieldContext,
        calls: Option<&'a ScalarExpressionEvidence>,
    ) -> Self {
        Self { hir, field, initial_values: BTreeMap::new(), calls }
    }

    pub(crate) fn evaluate(
        &self,
        expression: ExprId,
        variables: &BTreeMap<SymbolId, FieldValue>,
    ) -> Option<FieldValue> {
        eval_expression_with_calls(self.hir, self.field, expression, variables, self.calls)
    }
}

fn apply_update(
    analysis: &ForwardAnalysis<'_>,
    target: &AccessPath,
    operator: PostfixOperator,
    variables: &mut BTreeMap<SymbolId, FieldValue>,
) -> Result<(), &'static str> {
    if !target.steps.is_empty()
        || !analysis
            .hir
            .symbol(target.root)
            .is_some_and(|symbol| symbol.kind == SymbolKind::Variable)
    {
        return Err("unsupported update target");
    }
    let Some(previous) = variables.get(&target.root) else {
        return Err("unknown update value");
    };
    let one = analysis.field.canonical(1.into());
    let updated = match operator {
        PostfixOperator::Increment => analysis.field.add(previous, &one),
        PostfixOperator::Decrement => analysis.field.subtract(previous, &one),
    };
    variables.insert(target.root, updated);
    Ok(())
}

fn fixed_side(
    analysis: &ForwardAnalysis<'_>,
    access: ExprId,
    value: ExprId,
    variables: &BTreeMap<SymbolId, FieldValue>,
) -> Option<(AccessKey, FieldValue)> {
    let ExprKind::Access(path) = &analysis.hir.expression(access)?.kind else { return None };
    let key = key_for_path(analysis.hir, analysis.field, path, variables);
    if !key.exact_alias(&key) {
        return None;
    }
    let value = analysis.evaluate(value, variables)?;
    Some((key, value))
}

fn fixed_equation(
    analysis: &ForwardAnalysis<'_>,
    target: Option<&AccessPath>,
    left: ExprId,
    right: Option<ExprId>,
    variables: &BTreeMap<SymbolId, FieldValue>,
) -> Option<(AccessKey, FieldValue)> {
    if let Some(target) = target {
        let key = key_for_path(analysis.hir, analysis.field, target, variables);
        if !key.exact_alias(&key) {
            return None;
        }
        let value = analysis.evaluate(left, variables)?;
        return Some((key, value));
    }
    let right = right?;
    fixed_side(analysis, left, right, variables)
        .or_else(|| fixed_side(analysis, right, left, variables))
}

#[derive(Default)]
struct LinearForm {
    coefficients: BTreeMap<AccessKey, FieldValue>,
}

impl LinearForm {
    fn from_path(
        analysis: &ForwardAnalysis<'_>,
        path: &AccessPath,
        values: &BTreeMap<SymbolId, FieldValue>,
    ) -> Option<Self> {
        let symbol = analysis.hir.symbol(path.terminal)?;
        if symbol.kind != SymbolKind::Signal {
            return None;
        }
        let key = key_for_path(analysis.hir, analysis.field, path, values);
        if !key.exact_alias(&key) {
            return None;
        }
        let one = analysis.field.canonical(1.into());
        Some(Self { coefficients: BTreeMap::from([(key, one)]) })
    }

    fn scale(&mut self, field: &FieldContext, factor: &FieldValue) {
        for coefficient in self.coefficients.values_mut() {
            *coefficient = field.multiply(coefficient, factor);
        }
        self.coefficients.retain(|_, coefficient| !field.is_zero(coefficient));
    }

    fn add(&mut self, field: &FieldContext, other: Self) {
        for (key, coefficient) in other.coefficients {
            let value = if let Some(current) = self.coefficients.remove(&key) {
                field.add(&current, &coefficient)
            } else {
                coefficient
            };
            if !field.is_zero(&value) {
                self.coefficients.insert(key, value);
            }
        }
    }
}

trait LinearizeAccesses {
    fn linearize(
        &self,
        analysis: &ForwardAnalysis<'_>,
        values: &BTreeMap<SymbolId, FieldValue>,
    ) -> Option<LinearForm>;
}

impl LinearizeAccesses for ExprId {
    fn linearize(
        &self,
        analysis: &ForwardAnalysis<'_>,
        values: &BTreeMap<SymbolId, FieldValue>,
    ) -> Option<LinearForm> {
        if analysis.evaluate(*self, values).is_some() {
            return Some(LinearForm::default());
        }
        let expression = analysis.hir.expression(*self)?;
        match &expression.kind {
            ExprKind::Access(path) => LinearForm::from_path(analysis, path, values),
            ExprKind::Unary { operator: UnaryOperator::Negate, operand } => {
                let mut form = operand.linearize(analysis, values)?;
                let minus_one = analysis.field.canonical((-1).into());
                form.scale(analysis.field, &minus_one);
                Some(form)
            }
            ExprKind::Parallel(operand) => operand.linearize(analysis, values),
            ExprKind::Binary { operator: BinaryOperator::Add, left, right } => {
                let mut form = left.linearize(analysis, values)?;
                form.add(analysis.field, right.linearize(analysis, values)?);
                Some(form)
            }
            ExprKind::Binary { operator: BinaryOperator::Subtract, left, right } => {
                let mut form = left.linearize(analysis, values)?;
                let mut right = right.linearize(analysis, values)?;
                right.scale(analysis.field, &analysis.field.canonical((-1).into()));
                form.add(analysis.field, right);
                Some(form)
            }
            ExprKind::Binary { operator: BinaryOperator::Multiply, left, right } => {
                let (factor, operand) = if let Some(factor) = analysis.evaluate(*left, values) {
                    (factor, right)
                } else {
                    (analysis.evaluate(*right, values)?, left)
                };
                let mut form = operand.linearize(analysis, values)?;
                form.scale(analysis.field, &factor);
                Some(form)
            }
            ExprKind::Ternary { condition, yes, no } => {
                let condition = analysis.evaluate(*condition, values)?;
                let selected = if analysis.field.is_zero(&condition) { no } else { yes };
                selected.linearize(analysis, values)
            }
            ExprKind::Number(_)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Call { .. }
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Array(_)
            | ExprKind::Tuple(_)
            | ExprKind::Opaque(_) => None,
        }
    }
}

fn linear_constraint(
    analysis: &ForwardAnalysis<'_>,
    kind: &CfgNodeKind,
    values: &BTreeMap<SymbolId, FieldValue>,
) -> Option<LinearForm> {
    let CfgNodeKind::Constraint { target, left, right } = kind else { return None };
    let form = if let Some(path) = target {
        LinearForm::from_path(analysis, path, values)
    } else {
        left.linearize(analysis, values)
    };
    let mut form = form?;
    let opposite = if target.is_some() { Some(*left) } else { *right };
    let mut opposite = opposite?.linearize(analysis, values)?;
    opposite.scale(analysis.field, &analysis.field.canonical((-1).into()));
    form.add(analysis.field, opposite);
    Some(form)
}

/// Return exact nonzero linear coefficients when the full equality is supported.
pub(super) fn proven_linear_touches(
    analysis: &ForwardAnalysis<'_>,
    kind: &CfgNodeKind,
    values: &BTreeMap<SymbolId, FieldValue>,
) -> Option<BTreeSet<AccessKey>> {
    Some(linear_constraint(analysis, kind, values)?.coefficients.into_keys().collect())
}

fn constraint_touches(
    analysis: &ForwardAnalysis<'_>,
    kind: &CfgNodeKind,
    values: &BTreeMap<SymbolId, FieldValue>,
) -> BTreeSet<AccessKey> {
    proven_linear_touches(analysis, kind, values).unwrap_or_default()
}

pub fn expression_dependencies(
    analysis: &ForwardAnalysis<'_>,
    expression: ExprId,
    values: &BTreeMap<SymbolId, FieldValue>,
    variables: &BTreeMap<SymbolId, MayAccessSet>,
) -> Option<BTreeSet<AccessKey>> {
    let expr = analysis.hir.expression(expression)?;
    match &expr.kind {
        ExprKind::Number(_) => Some(BTreeSet::new()),
        ExprKind::Access(path) => access_dependencies(analysis, path, values, variables),
        ExprKind::Unary { operand, .. } | ExprKind::Parallel(operand) => {
            expression_dependencies(analysis, *operand, values, variables)
        }
        ExprKind::Binary { left, right, .. } => {
            expression_list_dependencies(analysis, &[*left, *right], values, variables)
        }
        ExprKind::Ternary { condition, yes, no } => {
            let mut result = expression_dependencies(analysis, *condition, values, variables)?;
            let arms = if let Some(value) = analysis.evaluate(*condition, values) {
                if analysis.field.is_zero(&value) {
                    vec![*no]
                } else {
                    vec![*yes]
                }
            } else {
                vec![*yes, *no]
            };
            result.extend(expression_list_dependencies(analysis, &arms, values, variables)?);
            Some(result)
        }
        ExprKind::Array(items) | ExprKind::Tuple(items) => {
            expression_list_dependencies(analysis, items, values, variables)
        }
        ExprKind::Call { target: CallTarget::Function(_), arguments } => {
            if let Some(indices) =
                analysis.calls.and_then(|calls| calls.call_input_dependencies(expression))
            {
                let mut result = BTreeSet::new();
                for index in indices {
                    let argument = arguments.get(*index)?;
                    result.extend(expression_dependencies(analysis, *argument, values, variables)?);
                }
                return Some(result);
            }
            expression_list_dependencies(analysis, arguments, values, variables)
        }
        ExprKind::AnonymousComponent { arguments, inputs, .. } => {
            let mut result = expression_list_dependencies(analysis, arguments, values, variables)?;
            for input in inputs {
                result.extend(expression_dependencies(analysis, input.value, values, variables)?);
            }
            Some(result)
        }
        ExprKind::Call { .. } | ExprKind::Opaque(_) => None,
    }
}

fn expression_list_dependencies(
    analysis: &ForwardAnalysis<'_>,
    expressions: &[ExprId],
    values: &BTreeMap<SymbolId, FieldValue>,
    variables: &BTreeMap<SymbolId, MayAccessSet>,
) -> Option<BTreeSet<AccessKey>> {
    let mut result = BTreeSet::new();
    for expression in expressions {
        result.extend(expression_dependencies(analysis, *expression, values, variables)?);
    }
    Some(result)
}

fn access_dependencies(
    analysis: &ForwardAnalysis<'_>,
    path: &AccessPath,
    values: &BTreeMap<SymbolId, FieldValue>,
    variables: &BTreeMap<SymbolId, MayAccessSet>,
) -> Option<BTreeSet<AccessKey>> {
    let mut result = BTreeSet::new();
    if analysis.hir.symbol(path.root).is_some_and(|symbol| symbol.kind == SymbolKind::Variable) {
        if !path.steps.is_empty() {
            return None;
        }
        result.extend(variables.get(&path.root)?.iter().cloned());
    } else {
        result.insert(key_for_path(analysis.hir, analysis.field, path, values));
    }
    for step in &path.steps {
        if let parser::hir::AccessStep::Index {
            index: parser::hir::ArrayIndex::Symbolic(id), ..
        } = step
        {
            result.extend(expression_dependencies(analysis, *id, values, variables)?);
        }
    }
    Some(result)
}

pub fn expression_degree(
    analysis: &ForwardAnalysis<'_>,
    expression: ExprId,
    values: &BTreeMap<SymbolId, FieldValue>,
    degrees: &BTreeMap<SymbolId, DegreeUpper>,
) -> DegreeUpper {
    let Some(expr) = analysis.hir.expression(expression) else { return DegreeUpper::Unbounded };
    match &expr.kind {
        ExprKind::Number(_) => DegreeUpper::Constant,
        ExprKind::Access(path) => match analysis.hir.symbol(path.root).map(|symbol| symbol.kind) {
            Some(SymbolKind::Parameter | SymbolKind::Tag) => DegreeUpper::Constant,
            Some(SymbolKind::Signal) => DegreeUpper::Linear,
            Some(SymbolKind::Variable) if path.steps.is_empty() => {
                degrees.get(&path.root).copied().unwrap_or(DegreeUpper::Unbounded)
            }
            Some(SymbolKind::Variable | SymbolKind::Component | SymbolKind::Bus) | None => {
                DegreeUpper::Unbounded
            }
        },
        ExprKind::Unary { operator: UnaryOperator::Negate, operand }
        | ExprKind::Parallel(operand) => expression_degree(analysis, *operand, values, degrees),
        ExprKind::Binary { operator, left, right } => {
            let left = expression_degree(analysis, *left, values, degrees);
            let right = expression_degree(analysis, *right, values, degrees);
            match operator {
                BinaryOperator::Add | BinaryOperator::Subtract => left.max(right),
                BinaryOperator::Multiply => left.multiply(right),
                _ => DegreeUpper::Unbounded,
            }
        }
        ExprKind::Ternary { condition, yes, no } => {
            if let Some(value) = analysis.evaluate(*condition, values) {
                let selected = if analysis.field.is_zero(&value) { no } else { yes };
                expression_degree(analysis, *selected, values, degrees)
            } else {
                expression_degree(analysis, *yes, values, degrees)
                    .max(expression_degree(analysis, *no, values, degrees))
            }
        }
        ExprKind::Call { .. }
            if analysis.calls.and_then(|calls| calls.call_value(expression)).is_some() =>
        {
            DegreeUpper::Constant
        }
        ExprKind::Unary { .. }
        | ExprKind::Call { .. }
        | ExprKind::AnonymousComponent { .. }
        | ExprKind::Array(_)
        | ExprKind::Tuple(_)
        | ExprKind::Opaque(_) => DegreeUpper::Unbounded,
    }
}

fn assign_degree(
    analysis: &ForwardAnalysis<'_>,
    target: &AccessPath,
    value: ExprId,
    variables: &BTreeMap<SymbolId, FieldValue>,
    degrees: &mut BTreeMap<SymbolId, DegreeUpper>,
) {
    let degree = if target.steps.is_empty() {
        expression_degree(analysis, value, variables, degrees)
    } else {
        DegreeUpper::Unbounded
    };
    if degree == DegreeUpper::Unbounded {
        degrees.remove(&target.root);
    } else {
        degrees.insert(target.root, degree);
    }
}

fn assign_dependencies(
    analysis: &ForwardAnalysis<'_>,
    target: &AccessPath,
    value: ExprId,
    variables: &BTreeMap<SymbolId, FieldValue>,
    dependencies: &mut BTreeMap<SymbolId, MayAccessSet>,
) {
    let dependency = if target.steps.is_empty() {
        expression_dependencies(analysis, value, variables, dependencies)
    } else {
        None
    };
    if let Some(dependency) = dependency {
        dependencies.insert(target.root, MayAccessSet::from_keys(dependency));
    } else {
        dependencies.remove(&target.root);
    }
}

fn assign_value(
    analysis: &ForwardAnalysis<'_>,
    target: &AccessPath,
    value: ExprId,
    variables: &mut BTreeMap<SymbolId, FieldValue>,
) {
    let value = if target.steps.is_empty() { analysis.evaluate(value, variables) } else { None };
    if let Some(value) = value {
        variables.insert(target.root, value);
    } else {
        variables.remove(&target.root);
    }
}

fn replace_symbolic(
    analysis: &ForwardAnalysis<'_>,
    target: &AccessPath,
    value: ExprId,
    variables: &BTreeMap<SymbolId, FieldValue>,
    symbolic: &mut Arc<MustSymbolicVariables>,
) {
    let scalar = target.steps.is_empty()
        && analysis.hir.symbol(target.root).is_some_and(|symbol| {
            symbol.kind == SymbolKind::Variable && symbol.rank == 0 && symbol.shape_checked
        });
    let value = if scalar {
        let inputs = NormalizationInputs::new(
            analysis.hir,
            analysis.field,
            variables,
            analysis.calls,
            symbolic,
        );
        variable_polynomial(&inputs, value).ok()
    } else {
        None
    };
    if let Some(value) = value {
        Arc::make_mut(symbolic).insert(target.root, value);
    } else {
        Arc::make_mut(symbolic).remove(target.root);
    }
}

fn accumulate_symbolic(
    analysis: &ForwardAnalysis<'_>,
    target: &AccessPath,
    value: ExprId,
    variables: &BTreeMap<SymbolId, FieldValue>,
    symbolic: &mut Arc<MustSymbolicVariables>,
) {
    let previous = symbolic.get(target.root).cloned();
    let inputs =
        NormalizationInputs::new(analysis.hir, analysis.field, variables, analysis.calls, symbolic);
    let value = variable_polynomial(&inputs, value).ok();
    if let (Some(mut previous), Some(value)) = (previous, value) {
        previous.add(analysis.field, value);
        Arc::make_mut(symbolic).insert(target.root, previous);
    } else {
        Arc::make_mut(symbolic).remove(target.root);
    }
}

fn accumulate_value(
    analysis: &ForwardAnalysis<'_>,
    target: &AccessPath,
    value: ExprId,
    variables: &mut BTreeMap<SymbolId, FieldValue>,
) {
    let value = variables
        .get(&target.root)
        .zip(analysis.evaluate(value, variables))
        .map(|(previous, value)| analysis.field.add(previous, &value));
    if let Some(value) = value {
        variables.insert(target.root, value);
    } else {
        variables.remove(&target.root);
    }
}

fn accumulate_dependencies(
    analysis: &ForwardAnalysis<'_>,
    target: &AccessPath,
    value: ExprId,
    variables: &BTreeMap<SymbolId, FieldValue>,
    dependencies: &mut BTreeMap<SymbolId, MayAccessSet>,
) {
    let value = expression_dependencies(analysis, value, variables, dependencies);
    let previous = dependencies.get(&target.root).cloned();
    if let (Some(mut previous), Some(value)) = (previous, value) {
        previous.join_assign(&MayAccessSet::from_keys(value));
        dependencies.insert(target.root, previous);
    } else {
        dependencies.remove(&target.root);
    }
}

fn accumulate_degree(
    analysis: &ForwardAnalysis<'_>,
    target: &AccessPath,
    value: ExprId,
    variables: &BTreeMap<SymbolId, FieldValue>,
    degrees: &mut BTreeMap<SymbolId, DegreeUpper>,
) {
    let previous = degrees.get(&target.root).copied();
    let degree = expression_degree(analysis, value, variables, degrees);
    if let Some(previous) = previous {
        let degree = previous.max(degree);
        if degree != DegreeUpper::Unbounded {
            degrees.insert(target.root, degree);
            return;
        }
    }
    degrees.remove(&target.root);
}

impl ForwardState {
    fn apply_assignment(
        &mut self,
        analysis: &ForwardAnalysis<'_>,
        target: &AccessPath,
        value: ExprId,
        operator: AssignmentOperator,
    ) -> Result<(), String> {
        let Self::Reached { variables, symbolic, dependencies, degrees, .. } = self else {
            return Ok(());
        };
        let scalar_variable = target.steps.is_empty()
            && analysis.hir.symbol(target.root).is_some_and(|symbol| {
                symbol.kind == SymbolKind::Variable && symbol.rank == 0 && symbol.shape_checked
            });
        if operator != AssignmentOperator::Assign
            && (operator != AssignmentOperator::Add || !scalar_variable)
        {
            variables.remove(&target.root);
            Arc::make_mut(symbolic).remove(target.root);
            dependencies.remove(&target.root);
            degrees.remove(&target.root);
            return Err(format!("unsupported compound assignment {operator:?}"));
        }
        if scalar_variable && operator == AssignmentOperator::Add {
            accumulate_symbolic(analysis, target, value, variables, symbolic);
            accumulate_degree(analysis, target, value, variables, degrees);
            accumulate_dependencies(analysis, target, value, variables, dependencies);
            accumulate_value(analysis, target, value, variables);
        } else if analysis
            .hir
            .symbol(target.root)
            .is_some_and(|symbol| symbol.kind == SymbolKind::Variable)
        {
            replace_symbolic(analysis, target, value, variables, symbolic);
            assign_degree(analysis, target, value, variables, degrees);
            assign_dependencies(analysis, target, value, variables, dependencies);
            assign_value(analysis, target, value, variables);
        }
        Ok(())
    }

    fn apply_deferred_assignment(
        &mut self,
        analysis: &ForwardAnalysis<'_>,
        target: &AccessPath,
        value: ExprId,
        operator: AssignmentOperator,
    ) -> Result<(), String> {
        let Self::Reached { variables, symbolic, dependencies, degrees, .. } = self else {
            return Ok(());
        };
        Arc::make_mut(symbolic).remove(target.root);
        if operator != AssignmentOperator::Assign {
            variables.remove(&target.root);
            dependencies.remove(&target.root);
            degrees.remove(&target.root);
            return Err(format!("unsupported compound assignment {operator:?}"));
        }
        let scalar = target.steps.is_empty()
            && analysis
                .hir
                .symbol(target.root)
                .is_some_and(|symbol| symbol.kind == SymbolKind::Variable)
            && analysis.evaluate(value, variables).is_some();
        if !scalar {
            return Err("deferred assignment shape".into());
        }
        assign_degree(analysis, target, value, variables, degrees);
        assign_dependencies(analysis, target, value, variables, dependencies);
        assign_value(analysis, target, value, variables);
        Ok(())
    }

    fn apply_declaration(
        &mut self,
        analysis: &ForwardAnalysis<'_>,
        symbol: SymbolId,
    ) -> Result<(), String> {
        let Self::Reached { variables, symbolic, dependencies, degrees, .. } = self else {
            return Ok(());
        };
        let Some(declared) = analysis.hir.symbol(symbol) else {
            return Err("missing declaration symbol".into());
        };
        if declared.kind == SymbolKind::Variable {
            dependencies.insert(symbol, MayAccessSet::default());
            if declared.rank == 0 && declared.shape_checked {
                let zero = analysis.field.canonical(0.into());
                Arc::make_mut(symbolic)
                    .insert(symbol, ExpressionPolynomial::constant(analysis.field, zero.clone()));
                variables.insert(symbol, zero);
                degrees.insert(symbol, DegreeUpper::Constant);
            } else {
                Arc::make_mut(symbolic).remove(symbol);
                variables.remove(&symbol);
                degrees.remove(&symbol);
            }
        }
        Ok(())
    }

    fn apply_update(
        &mut self,
        analysis: &ForwardAnalysis<'_>,
        target: &AccessPath,
        operator: PostfixOperator,
    ) -> Result<(), String> {
        let Self::Reached { variables, symbolic, degrees, .. } = self else { return Ok(()) };
        let previous = symbolic.get(target.root).cloned();
        if let Err(reason) = apply_update(analysis, target, operator, variables) {
            Arc::make_mut(symbolic).remove(target.root);
            return Err(reason.into());
        }
        if let Some(mut previous) = previous {
            let one = analysis.field.canonical(1.into());
            let delta = match operator {
                PostfixOperator::Increment => one,
                PostfixOperator::Decrement => analysis.field.negate(&one),
            };
            previous.add(analysis.field, ExpressionPolynomial::constant(analysis.field, delta));
            Arc::make_mut(symbolic).insert(target.root, previous);
        } else {
            Arc::make_mut(symbolic).remove(target.root);
        }
        degrees.insert(target.root, DegreeUpper::Constant);
        Ok(())
    }

    fn apply_constraint(
        &mut self,
        analysis: &ForwardAnalysis<'_>,
        node: &CfgNode,
    ) -> Result<(), String> {
        let Self::Reached {
            variables,
            symbolic,
            may_constraints,
            must_constraints,
            must_touches,
            must_fixed,
            must_equations,
            ..
        } = self
        else {
            return Ok(());
        };
        let CfgNodeKind::Constraint { target, left, right } = &node.kind else {
            return Err("expected constraint node".into());
        };
        may_constraints.insert(node.id);
        must_constraints.insert(node.id);
        must_touches.extend(constraint_touches(analysis, &node.kind, variables));
        if let Some((key, value)) =
            fixed_equation(analysis, target.as_ref(), *left, *right, variables)
        {
            must_fixed.insert((key, value));
        }
        let inputs = NormalizationInputs::new(
            analysis.hir,
            analysis.field,
            variables,
            analysis.calls,
            symbolic,
        );
        match constraint_equation(&inputs, &node.kind) {
            Ok(equation) => Arc::make_mut(must_equations).insert(equation, node.id),
            Err(_) => Arc::make_mut(must_equations).block(node.id),
        }
        Ok(())
    }

    fn apply_opaque_assignment(
        &mut self,
        analysis: &ForwardAnalysis<'_>,
        target: &AccessPath,
        value: ExprId,
    ) {
        let Self::Reached { variables, symbolic, dependencies, degrees, .. } = self else {
            return;
        };
        Arc::make_mut(symbolic).remove(target.root);
        if analysis
            .hir
            .symbol(target.root)
            .is_some_and(|symbol| symbol.kind == SymbolKind::Variable)
        {
            assign_degree(analysis, target, value, variables, degrees);
            assign_dependencies(analysis, target, value, variables, dependencies);
            assign_value(analysis, target, value, variables);
        }
    }

    fn check_evaluate(analysis: &ForwardAnalysis<'_>, expression: ExprId) -> Result<(), String> {
        let Some(expression) = analysis.hir.expression(expression) else {
            return Err("missing expression".into());
        };
        if let ExprKind::Opaque(reason) = &expression.kind {
            return Err(format!("{reason:?}"));
        }
        if let ExprKind::AnonymousComponent { .. } = &expression.kind {
            return Err("external component summary".into());
        }
        Ok(())
    }

    fn apply_node(&mut self, analysis: &ForwardAnalysis<'_>, node: &CfgNode) -> Result<(), String> {
        if let Self::Unreachable = self {
            return Ok(());
        }
        match &node.kind {
            CfgNodeKind::Evaluate(id) => Self::check_evaluate(analysis, *id),
            CfgNodeKind::Assignment { target, value, operator } => {
                self.apply_assignment(analysis, target, *value, *operator)
            }
            CfgNodeKind::DeferredAssignment { target, value, operator } => {
                self.apply_deferred_assignment(analysis, target, *value, *operator)
            }
            CfgNodeKind::Declaration { symbol } => self.apply_declaration(analysis, *symbol),
            CfgNodeKind::Update { target, operator } => {
                self.apply_update(analysis, target, *operator)
            }
            CfgNodeKind::Constraint { .. } => self.apply_constraint(analysis, node),
            CfgNodeKind::Opaque(reason) | CfgNodeKind::OpaqueEquality { reason, .. } => {
                Err(format!("{reason:?}"))
            }
            CfgNodeKind::OpaqueAssignment { target, value, reason, .. } => {
                self.apply_opaque_assignment(analysis, target, *value);
                Err(format!("{reason:?}"))
            }
            CfgNodeKind::DeferredAssert { condition } => {
                let Some(variables) = self.variables() else { return Ok(()) };
                if analysis.evaluate(*condition, variables).is_none() {
                    return Err("deferred assertion shape".into());
                }
                Ok(())
            }
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::LoopHeader
            | CfgNodeKind::Branch { .. }
            | CfgNodeKind::Witness { .. }
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Assert { .. }
            | CfgNodeKind::Log
            | CfgNodeKind::Instantiate { .. } => Ok(()),
        }
    }
}

impl DataflowAnalysis<DefinitionCfg> for ForwardAnalysis<'_> {
    type State = ForwardState;
    type Reason = String;

    fn boundary(&self, _: NodeId) -> Self::State {
        ForwardState::with_scalar_parameters(&self.initial_values)
    }
}

impl Transfer<ForwardAnalysis<'_>, ForwardState, String> for CfgNode {
    fn apply(
        &self,
        analysis: &ForwardAnalysis<'_>,
        input: &ForwardState,
    ) -> TransferOutcome<ForwardState, String> {
        let mut output = input.clone();
        match output.apply_node(analysis, self) {
            Ok(()) => TransferOutcome::Known(output),
            Err(reason) => TransferOutcome::Opaque { provisional: output, reason },
        }
    }
}

impl Transfer<ForwardAnalysis<'_>, ForwardState, String> for CfgEdge {
    fn apply(
        &self,
        analysis: &ForwardAnalysis<'_>,
        input: &ForwardState,
    ) -> TransferOutcome<ForwardState, String> {
        let Some(condition) = self.condition else {
            return TransferOutcome::Known(input.clone());
        };
        let Some(variables) = input.variables() else {
            return TransferOutcome::Known(ForwardState::Unreachable);
        };
        let Some(value) = analysis.evaluate(condition, variables) else {
            return TransferOutcome::Known(input.clone());
        };
        let truth = !analysis.field.is_zero(&value);
        let taken = match self.kind {
            EdgeKind::True => truth,
            EdgeKind::False => !truth,
            EdgeKind::Normal | EdgeKind::Loop | EdgeKind::Return => true,
        };
        TransferOutcome::Known(if taken { input.clone() } else { ForwardState::Unreachable })
    }
}

/// Evaluate only proven compile-time expressions in a concrete variable environment.
pub fn eval_expression(
    hir: &HirProject,
    field: &FieldContext,
    id: ExprId,
    variables: &BTreeMap<SymbolId, FieldValue>,
) -> Option<FieldValue> {
    eval_expression_with_calls(hir, field, id, variables, None)
}

pub(crate) fn eval_expression_with_calls(
    hir: &HirProject,
    field: &FieldContext,
    id: ExprId,
    variables: &BTreeMap<SymbolId, FieldValue>,
    calls: Option<&ScalarExpressionEvidence>,
) -> Option<FieldValue> {
    let expression = hir.expression(id)?;
    match &expression.kind {
        ExprKind::Number(text) => field.parse(text),
        ExprKind::Access(path) if path.steps.is_empty() => variables.get(&path.root).cloned(),
        ExprKind::Unary { operator, operand } => {
            let value = eval_expression_with_calls(hir, field, *operand, variables, calls)?;
            match operator {
                UnaryOperator::Negate => Some(field.negate(&value)),
                UnaryOperator::BooleanNot => {
                    Some(field.canonical(i32::from(field.is_zero(&value)).into()))
                }
                UnaryOperator::Complement => None,
            }
        }
        ExprKind::Binary { operator, left, right } => {
            let left = eval_expression_with_calls(hir, field, *left, variables, calls)?;
            let right = eval_expression_with_calls(hir, field, *right, variables, calls)?;
            match operator {
                BinaryOperator::Add => Some(field.add(&left, &right)),
                BinaryOperator::Subtract => Some(field.subtract(&left, &right)),
                BinaryOperator::Multiply => Some(field.multiply(&left, &right)),
                BinaryOperator::Power => field.bounded_power(&left, &right),
                BinaryOperator::ShiftLeft => {
                    field.bounded_shift(&left, &right, ShiftDirection::Left)
                }
                BinaryOperator::ShiftRight => {
                    field.bounded_shift(&left, &right, ShiftDirection::Right)
                }
                BinaryOperator::Equal => Some(field.canonical(i32::from(left == right).into())),
                BinaryOperator::NotEqual => Some(field.canonical(i32::from(left != right).into())),
                BinaryOperator::Less => Some(field.canonical(
                    i32::from(field.compare_signed(&left, &right) == Ordering::Less).into(),
                )),
                BinaryOperator::LessEqual => Some(field.canonical(
                    i32::from(field.compare_signed(&left, &right) != Ordering::Greater).into(),
                )),
                BinaryOperator::Greater => Some(field.canonical(
                    i32::from(field.compare_signed(&left, &right) == Ordering::Greater).into(),
                )),
                BinaryOperator::GreaterEqual => Some(field.canonical(
                    i32::from(field.compare_signed(&left, &right) != Ordering::Less).into(),
                )),
                BinaryOperator::BooleanOr
                | BinaryOperator::BooleanAnd
                | BinaryOperator::BitOr
                | BinaryOperator::BitXor
                | BinaryOperator::BitAnd
                | BinaryOperator::Divide
                | BinaryOperator::IntegerDivide
                | BinaryOperator::Modulo => None,
            }
        }
        ExprKind::Ternary { condition, yes, no } => {
            let condition = eval_expression_with_calls(hir, field, *condition, variables, calls)?;
            let selected = if field.is_zero(&condition) { no } else { yes };
            eval_expression_with_calls(hir, field, *selected, variables, calls)
        }
        ExprKind::Parallel(operand) => {
            eval_expression_with_calls(hir, field, *operand, variables, calls)
        }
        ExprKind::Call { target: CallTarget::Function(_), .. } => calls?.call_value(id).cloned(),
        ExprKind::Access(_)
        | ExprKind::Call { .. }
        | ExprKind::AnonymousComponent { .. }
        | ExprKind::Array(_)
        | ExprKind::Tuple(_)
        | ExprKind::Opaque(_) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use abstract_interpretation::graph::FlowGraph;
    use abstract_interpretation::solver::{solve, Forward, SolveResult};
    use parser::hir::lift_project;
    use parser::new_frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;
    use std::fs;

    #[test]
    fn compile_time_power_requires_a_bounded_nonnegative_exponent() {
        let directory =
            std::env::temp_dir().join(format!("circomspect-exponent-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(&source, "function F(i){return 2**i;}").unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let expression = hir.expressions().iter().find_map(|expression| {
            let ExprKind::Binary { operator: BinaryOperator::Power, .. } = expression.kind else {
                return None;
            };
            Some(expression.id)
        });
        let expression = expression.unwrap();
        let parameter = hir.symbols().iter().find(|symbol| symbol.name == "i").unwrap().id;
        for curve in [Curve::Bn254, Curve::Goldilocks] {
            let field = FieldContext::for_curve(curve);
            for exponent in [0usize, 1, 64, 254, 512] {
                let value = field.canonical(exponent.into());
                let variables = BTreeMap::from([(parameter, value)]);
                let result = eval_expression(&hir, &field, expression, &variables);
                let expected = field.canonical(num_bigint::BigInt::from(1u8) << exponent);
                assert_eq!(result, Some(expected));
            }
            for exponent in [513_i32, -1] {
                let value = field.canonical(exponent.into());
                let variables = BTreeMap::from([(parameter, value)]);
                assert_eq!(eval_expression(&hir, &field, expression, &variables), None);
            }
            assert_eq!(eval_expression(&hir, &field, expression, &BTreeMap::new()), None);
        }
    }

    #[test]
    fn proved_induction_update_retains_constant_symbolic_shape_monotonically() {
        let directory =
            std::env::temp_dir().join(format!("circomspect-induction-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(&source, "function F(){var i=0;i++;return i;}").unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("F").unwrap()).unwrap();
        let node = cfg
            .nodes()
            .iter()
            .filter_map(|site| cfg.node(*site))
            .find(|node| {
                let CfgNodeKind::Update { .. } = &node.kind else { return false };
                true
            })
            .unwrap();
        let i = hir.symbols().iter().find(|symbol| symbol.name == "i").unwrap().id;
        let field = FieldContext::for_curve(Curve::Bn254);
        let zero = field.canonical(0.into());
        let one = field.canonical(1.into());
        let mut precise = ForwardState::boundary();
        let ForwardState::Reached { variables, symbolic, .. } = &mut precise else {
            panic!("reached boundary")
        };
        variables.insert(i, zero.clone());
        Arc::make_mut(symbolic).insert(i, ExpressionPolynomial::constant(&field, zero.clone()));
        let mut broad = ForwardState::boundary();
        let ForwardState::Reached { variables, .. } = &mut broad else {
            panic!("reached boundary")
        };
        variables.insert(i, zero);
        assert!(precise.leq(&broad));
        let analysis = ForwardAnalysis::new(&hir, &field);
        let TransferOutcome::Known(precise) = node.apply(&analysis, &precise) else {
            panic!("proved induction update")
        };
        let TransferOutcome::Known(broad) = node.apply(&analysis, &broad) else {
            panic!("proved induction update")
        };
        assert!(precise.leq(&broad));
        assert_eq!(precise.variables().unwrap().get(&i), Some(&one));
        assert_eq!(broad.variables().unwrap().get(&i), Some(&one));
        assert_eq!(
            precise.symbolic().unwrap().get(i),
            Some(&ExpressionPolynomial::constant(&field, one))
        );
        assert!(broad.symbolic().unwrap().get(i).is_none());
    }

    fn exit_value(alternative: &str) -> Option<FieldValue> {
        let directory = std::env::temp_dir()
            .join(format!("circomspect-phase4-join-{}-{alternative}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(
            &source,
            format!(
                "function Check(n){{var x=0; if(n){{x=1;}}else{{x={alternative};}} return x;}}"
            ),
        )
        .unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let definition = hir.definition("Check").unwrap();
        let cfg = crate::hir_cfg::build_cfg(&hir, definition).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let SolveResult::Complete(states) =
            solve::<_, _, Forward>(&cfg, &ForwardAnalysis::new(&hir, &field), None).unwrap()
        else {
            panic!("complete local solver")
        };
        let x = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap().id;
        states.get(&cfg.exit())?.output.as_ref()?.variables()?.get(&x).cloned()
    }

    #[test]
    fn late_predecessor_requeues_the_real_hir_join() {
        let one = FieldContext::for_curve(Curve::Bn254).canonical(1.into());
        assert_eq!(exit_value("1"), Some(one));
        assert_eq!(exit_value("2"), None);
    }

    #[test]
    fn deferred_assignment_transfer_is_monotone_when_scalar_shape_is_proved() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-deferred-transfer-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(&source, "function F(n){var x=n;return x;}").unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let definition = hir.definition("F").unwrap();
        let cfg = crate::hir_cfg::build_cfg(&hir, definition).unwrap();
        let node = cfg
            .nodes()
            .iter()
            .filter_map(|id| cfg.node(*id))
            .find(|node| matches!(node.kind, CfgNodeKind::DeferredAssignment { .. }))
            .unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let parameter = hir.symbols().iter().find(|symbol| symbol.name == "n").unwrap().id;
        let local = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap().id;
        let one = field.canonical(1.into());
        let mut precise =
            ForwardState::with_scalar_parameters(&BTreeMap::from([(parameter, one.clone())]));
        let broad = precise.clone();
        let ForwardState::Reached { variables, .. } = &mut precise else { panic!("reached") };
        variables.insert(local, field.canonical(0.into()));
        assert!(precise.leq(&broad));
        let analysis = ForwardAnalysis::new(&hir, &field);
        let TransferOutcome::Known(left) = node.apply(&analysis, &precise) else {
            panic!("proved scalar transfer")
        };
        let TransferOutcome::Known(right) = node.apply(&analysis, &broad) else {
            panic!("proved scalar transfer")
        };
        assert!(left.leq(&right));
        assert_eq!(right.variables().unwrap().get(&local), Some(&one));
        assert!(matches!(
            node.apply(&analysis, &ForwardState::boundary()),
            TransferOutcome::Opaque { .. }
        ));
    }

    #[test]
    fn relation_blockers_do_not_break_constraint_transfer_monotonicity() {
        let directory = std::env::temp_dir()
            .join(format!("circomspect-relation-monotone-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(&source, "template T(){var v=1;signal input a;signal output x;x===v+a*a*a;}")
            .unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("T").unwrap()).unwrap();
        let constraint = cfg
            .nodes()
            .iter()
            .find_map(|id| {
                let node = cfg.node(*id)?;
                if let CfgNodeKind::Constraint { .. } = node.kind {
                    Some(node)
                } else {
                    None
                }
            })
            .unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let variable = hir.symbols().iter().find(|item| item.name == "v").unwrap().id;
        let precise = ForwardState::with_scalar_parameters(&BTreeMap::from([(
            variable,
            field.canonical(1.into()),
        )]));
        let broad = ForwardState::boundary();
        assert!(precise.leq(&broad));
        let analysis = ForwardAnalysis::new(&hir, &field);
        let TransferOutcome::Known(left) = constraint.apply(&analysis, &precise) else {
            panic!("constraint transfer")
        };
        let TransferOutcome::Known(right) = constraint.apply(&analysis, &broad) else {
            panic!("constraint transfer")
        };
        assert!(left.leq(&right));
    }

    #[test]
    fn unsupported_compound_write_drops_old_scalar_facts_monotonically() {
        let directory = std::env::temp_dir()
            .join(format!("circomspect-phase5-compound-transfer-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(&source, "function F(){var x=1;x*=1;return x;}").unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("F").unwrap()).unwrap();
        let node = cfg
            .nodes()
            .iter()
            .filter_map(|id| cfg.node(*id))
            .find(|node| {
                let CfgNodeKind::Assignment { operator, .. } = node.kind else { return false };
                operator == AssignmentOperator::Multiply
            })
            .unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let x = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap().id;
        let precise =
            ForwardState::with_scalar_parameters(&BTreeMap::from([(x, field.canonical(1.into()))]));
        let broad = ForwardState::boundary();
        assert!(precise.leq(&broad));
        let analysis = ForwardAnalysis::new(&hir, &field);
        let TransferOutcome::Opaque { provisional: left, .. } = node.apply(&analysis, &precise)
        else {
            panic!("compound transfer must be opaque")
        };
        let TransferOutcome::Opaque { provisional: right, .. } = node.apply(&analysis, &broad)
        else {
            panic!("compound transfer must be opaque")
        };
        assert!(left.leq(&right));
        assert!(!left.variables().unwrap().contains_key(&x));
        assert!(!left.dependencies().unwrap().contains_key(&x));
        assert!(!left.degrees().unwrap().contains_key(&x));
    }

    #[test]
    fn symbolic_shape_and_exact_scalar_fallback_transfer_monotonically() {
        let directory = std::env::temp_dir()
            .join(format!("circomspect-symbolic-transfer-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(&source, "template T(){signal input a;var x=a-a+1;var y=x+1;x+=1;}").unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("T").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let x = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap().id;
        let y = hir.symbols().iter().find(|symbol| symbol.name == "y").unwrap().id;
        let mut x_value = None;
        let mut transfers = Vec::new();
        for site in cfg.nodes() {
            let Some(node) = cfg.node(*site) else { panic!("CFG site must exist") };
            if let CfgNodeKind::Assignment { target, value, .. } = &node.kind {
                if target.root == x && x_value.is_none() {
                    x_value = Some(*value);
                }
                if target.root == x || target.root == y {
                    transfers.push(node);
                }
            }
        }
        let values = BTreeMap::new();
        let symbolic = MustSymbolicVariables::reachable_empty();
        let inputs = NormalizationInputs::new(&hir, &field, &values, None, &symbolic);
        let x_polynomial = variable_polynomial(&inputs, x_value.unwrap()).unwrap();
        let mut precise = ForwardState::boundary();
        let ForwardState::Reached { variables, symbolic, .. } = &mut precise else {
            panic!("reached boundary")
        };
        variables.insert(x, field.canonical(1.into()));
        Arc::make_mut(symbolic).insert(x, x_polynomial);
        let mut broad = ForwardState::boundary();
        let ForwardState::Reached { variables, .. } = &mut broad else {
            panic!("reached boundary")
        };
        variables.insert(x, field.canonical(1.into()));
        assert!(precise.leq(&broad));
        let analysis = ForwardAnalysis::new(&hir, &field);
        for transfer in transfers {
            let precise_after = transfer_state(transfer.apply(&analysis, &precise));
            let broad_after = transfer_state(transfer.apply(&analysis, &broad));
            assert!(precise_after.leq(&broad_after), "{precise_after:?} <= {broad_after:?}");
            assert_eq!(precise_after.variables(), broad_after.variables());
            if let CfgNodeKind::Assignment { target, .. } = &transfer.kind {
                if target.root == y {
                    assert!(precise_after.symbolic().unwrap().get(y).is_some());
                    assert!(broad_after.symbolic().unwrap().get(y).is_none());
                }
            }
        }
    }

    #[test]
    fn branch_equations_join_by_value_instead_of_site_id() {
        fn fixed(alternative: &str) -> Option<FieldValue> {
            let directory = std::env::temp_dir()
                .join(format!("circomspect-phase4-fixed-{}-{alternative}", std::process::id()));
            fs::create_dir_all(&directory).unwrap();
            let source = directory.join("case.circom");
            fs::write(
                &source,
                format!(
                    "template Check(n){{signal input x; if(n){{x===1;}}else{{x==={alternative};}}}}"
                ),
            )
            .unwrap();
            let loaded =
                load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
            let hir = lift_project(&loaded).hir;
            let definition = hir.definition("Check").unwrap();
            let cfg = crate::hir_cfg::build_cfg(&hir, definition).unwrap();
            let field = FieldContext::for_curve(Curve::Bn254);
            let SolveResult::Complete(states) =
                solve::<_, _, Forward>(&cfg, &ForwardAnalysis::new(&hir, &field), None).unwrap()
            else {
                panic!("complete local solver")
            };
            let path = hir
                .expressions()
                .iter()
                .find_map(|expr| {
                    let ExprKind::Access(path) = &expr.kind else { return None };
                    hir.symbol(path.root).is_some_and(|symbol| symbol.name == "x").then_some(path)
                })
                .unwrap();
            let key = super::super::access::key_for_path(&hir, &field, path, &BTreeMap::new());
            let state = states.get(&cfg.exit())?.output.as_ref()?;
            let values: BTreeSet<_> = state
                .fixed_equations()?
                .iter()
                .filter_map(|(access, value)| (access == &key).then_some(value.clone()))
                .collect();
            (values.len() == 1).then(|| values.into_iter().next()).flatten()
        }

        let one = FieldContext::for_curve(Curve::Bn254).canonical(1.into());
        assert_eq!(fixed("1"), Some(one));
        assert_eq!(fixed("2"), None);
    }

    #[test]
    fn must_fixed_value_domain_obeys_join_laws() {
        let directory = std::env::temp_dir()
            .join(format!("circomspect-phase4-fixed-laws-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(&source, "template T(){signal input x; x===1;}").unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let root = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap().id;
        let key = AccessKey { root, instance: None, steps: Vec::new() };
        let field = FieldContext::for_curve(Curve::Bn254);
        let one = field.canonical(1.into());
        let two = field.canonical(2.into());
        let fixed = [
            BTreeSet::from([(key.clone(), one.clone())]),
            BTreeSet::from([(key.clone(), two.clone())]),
            BTreeSet::from([(key.clone(), one), (key.clone(), two)]),
        ];
        let mut states = vec![ForwardState::Unreachable, ForwardState::boundary()];
        for equations in fixed {
            let mut state = ForwardState::boundary();
            let ForwardState::Reached { must_fixed, .. } = &mut state else { panic!("reached") };
            *must_fixed = equations;
            states.push(state);
        }
        for a in &states {
            for b in &states {
                let mut joined = a.clone();
                joined.join_assign(b);
                assert!(a.leq(&joined));
                assert!(b.leq(&joined));
                let mut reverse = b.clone();
                reverse.join_assign(a);
                assert_eq!(joined, reverse);
                for c in &states {
                    let mut left = joined.clone();
                    left.join_assign(c);
                    let mut right = b.clone();
                    right.join_assign(c);
                    let mut other = a.clone();
                    other.join_assign(&right);
                    assert_eq!(left, other);
                }
            }
        }
        let definition = hir.definition("T").unwrap();
        let cfg = crate::hir_cfg::build_cfg(&hir, definition).unwrap();
        let constraint = cfg
            .nodes()
            .iter()
            .find_map(|id| {
                let node = cfg.node(*id)?;
                let CfgNodeKind::Constraint { .. } = &node.kind else { return None };
                Some(node)
            })
            .unwrap();
        let analysis = ForwardAnalysis::new(&hir, &field);
        for left in &states {
            for right in &states {
                if !left.leq(right) {
                    continue;
                }
                let TransferOutcome::Known(left_after) = constraint.apply(&analysis, left) else {
                    panic!("known constraint transfer")
                };
                let TransferOutcome::Known(right_after) = constraint.apply(&analysis, right) else {
                    panic!("known constraint transfer")
                };
                assert!(left_after.leq(&right_after));
            }
        }
    }

    fn states() -> Vec<ForwardState> {
        let mut values = vec![ForwardState::Unreachable];
        for may_bits in 0..4_u8 {
            for must_bits in 0..4_u8 {
                if must_bits & !may_bits != 0 {
                    continue;
                }
                let may_constraints =
                    (0..2).filter(|bit| may_bits & (1 << bit) != 0).map(NodeId::new).collect();
                let must_constraints =
                    (0..2).filter(|bit| must_bits & (1 << bit) != 0).map(NodeId::new).collect();
                values.push(ForwardState::Reached {
                    variables: BTreeMap::new(),
                    symbolic: Arc::new(MustSymbolicVariables::reachable_empty()),
                    dependencies: BTreeMap::new(),
                    degrees: BTreeMap::new(),
                    may_constraints,
                    must_constraints,
                    must_touches: BTreeSet::new(),
                    must_fixed: BTreeSet::new(),
                    must_equations: Arc::new(MustEquations::reachable_empty()),
                });
            }
        }
        values
    }

    #[test]
    fn production_may_must_state_obeys_lattice_laws() {
        let values = states();
        for a in &values {
            assert!(ForwardState::bottom().leq(a));
            for b in &values {
                let mut joined = a.clone();
                let changed = joined.join_assign(b);
                assert_eq!(changed, joined != *a);
                assert!(a.leq(&joined));
                assert!(b.leq(&joined));
                let mut reverse = b.clone();
                reverse.join_assign(a);
                assert_eq!(joined, reverse);
                for c in &values {
                    let mut left = joined.clone();
                    left.join_assign(c);
                    let mut right = b.clone();
                    right.join_assign(c);
                    let mut other = a.clone();
                    other.join_assign(&right);
                    assert_eq!(left, other);
                }
            }
        }
    }

    #[test]
    fn symbolic_index_dependency_transfer_respects_precision_order() {
        let directory = std::env::temp_dir()
            .join(format!("circomspect-phase4-index-law-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(
            &source,
            "template T(){signal input a[2]; var i=0; var t=a[i]; signal output y; y<==t;}",
        )
        .unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("T").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let i = hir.symbols().iter().find(|symbol| symbol.name == "i").unwrap().id;
        let t = hir.symbols().iter().find(|symbol| symbol.name == "t").unwrap().id;
        let assignment = cfg
            .nodes()
            .iter()
            .filter_map(|id| cfg.node(*id))
            .find(|node| match &node.kind {
                CfgNodeKind::Assignment { target, .. } => target.root == t,
                _ => false,
            })
            .unwrap();
        let mut precise = ForwardState::boundary();
        let ForwardState::Reached { variables, dependencies, .. } = &mut precise else {
            panic!("reached")
        };
        variables.insert(i, field.canonical(0.into()));
        dependencies.insert(i, MayAccessSet::default());
        let mut unknown = ForwardState::boundary();
        let ForwardState::Reached { dependencies, .. } = &mut unknown else { panic!("reached") };
        dependencies.insert(i, MayAccessSet::default());
        assert!(precise.leq(&unknown));
        let analysis = ForwardAnalysis::new(&hir, &field);
        let TransferOutcome::Known(precise) = assignment.apply(&analysis, &precise) else {
            panic!("known assignment")
        };
        let TransferOutcome::Known(unknown) = assignment.apply(&analysis, &unknown) else {
            panic!("known assignment")
        };
        assert!(precise.leq(&unknown));
        let precise = precise.dependencies().unwrap().get(&t).unwrap();
        let unknown = unknown.dependencies().unwrap().get(&t).unwrap();
        assert!(precise.leq(unknown));
    }

    #[test]
    fn opaque_call_assignment_propagates_argument_may_dependencies_monotonically() {
        let directory = std::env::temp_dir()
            .join(format!("circomspect-phase4-call-law-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(
            &source,
            "function F(a){return a;} template T(){signal input x;var u=x;var t=F(u);\
             signal output y;y<==t;}",
        )
        .unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("T").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let x = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap().id;
        let u = hir.symbols().iter().find(|symbol| symbol.name == "u").unwrap().id;
        let t = hir.symbols().iter().find(|symbol| symbol.name == "t").unwrap().id;
        let key = AccessKey { root: x, instance: None, steps: Vec::new() };
        let node = cfg
            .nodes()
            .iter()
            .filter_map(|id| cfg.node(*id))
            .find(|node| match &node.kind {
                CfgNodeKind::OpaqueAssignment { target, .. } => target.root == t,
                _ => false,
            })
            .unwrap();
        let analysis = ForwardAnalysis::new(&hir, &field);
        check_transfer_order(node, &analysis, &variable_states(u, key.clone(), &field));
        let mut state = ForwardState::boundary();
        let ForwardState::Reached { dependencies, .. } = &mut state else { panic!("reached") };
        dependencies.insert(u, MayAccessSet::from_keys(BTreeSet::from([key.clone()])));
        let outcome = node.apply(&analysis, &state);
        assert!(matches!(outcome, TransferOutcome::Opaque { .. }));
        let state = transfer_state(outcome);
        assert!(state.dependencies().unwrap().get(&t).unwrap().iter().any(|item| item == &key));
    }

    fn transfer_state(outcome: TransferOutcome<ForwardState, String>) -> ForwardState {
        match outcome {
            TransferOutcome::Known(state) | TransferOutcome::Opaque { provisional: state, .. } => {
                state
            }
        }
    }

    fn check_transfer_order<'a, T>(
        transfer: &T,
        analysis: &ForwardAnalysis<'a>,
        states: &[ForwardState],
    ) where
        T: Transfer<ForwardAnalysis<'a>, ForwardState, String>,
    {
        for left in states {
            for right in states {
                if !left.leq(right) {
                    continue;
                }
                let left_after = transfer_state(transfer.apply(analysis, left));
                let right_after = transfer_state(transfer.apply(analysis, right));
                assert!(left_after.leq(&right_after), "{left:?} <= {right:?}");
            }
        }
    }

    fn variable_states(
        symbol: SymbolId,
        dependency: AccessKey,
        field: &FieldContext,
    ) -> Vec<ForwardState> {
        let mut states = vec![ForwardState::Unreachable, ForwardState::boundary()];
        for value in [None, Some(0), Some(1)] {
            for dependencies in
                [None, Some(BTreeSet::new()), Some(BTreeSet::from([dependency.clone()]))]
            {
                for degree in [None, Some(DegreeUpper::Constant), Some(DegreeUpper::Linear)] {
                    let mut state = ForwardState::boundary();
                    let ForwardState::Reached { variables, dependencies: facts, degrees, .. } =
                        &mut state
                    else {
                        panic!("reached")
                    };
                    if let Some(value) = value {
                        variables.insert(symbol, field.canonical(value.into()));
                    }
                    if let Some(dependencies) = &dependencies {
                        facts.insert(symbol, MayAccessSet::from_keys(dependencies.clone()));
                    }
                    if let Some(degree) = degree {
                        degrees.insert(symbol, degree);
                    }
                    states.push(state);
                }
            }
        }
        states
    }

    #[test]
    fn production_forward_node_and_edge_transfers_are_monotone() {
        let directory = std::env::temp_dir()
            .join(format!("circomspect-phase4-transfer-laws-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(
            &source,
            "template T(){signal input x; var t=x; t++; t=1<<t; t=t>>1; signal output y; \
             y<==t; if(1){y===1;}else{y===2;}}",
        )
        .unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("T").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let t = hir.symbols().iter().find(|symbol| symbol.name == "t").unwrap().id;
        let x = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap().id;
        let key = AccessKey { root: x, instance: None, steps: Vec::new() };
        let states = variable_states(t, key, &field);
        let analysis = ForwardAnalysis::new(&hir, &field);
        for id in cfg.nodes() {
            check_transfer_order(cfg.node(*id).unwrap(), &analysis, &states);
        }
        for id in cfg.edges() {
            check_transfer_order(cfg.edge(*id).unwrap().payload, &analysis, &states);
        }
    }

    #[test]
    fn compile_time_branch_edges_prune_monotonically() {
        let directory = std::env::temp_dir()
            .join(format!("circomspect-phase4-edge-laws-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(&source, "function T(){var t=0;if(t){return 1;}else{return 2;}}").unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("T").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let t = hir.symbols().iter().find(|symbol| symbol.name == "t").unwrap().id;
        let key = AccessKey { root: t, instance: None, steps: Vec::new() };
        let states = variable_states(t, key, &field);
        let analysis = ForwardAnalysis::new(&hir, &field);
        let edges: Vec<_> = cfg
            .edges()
            .iter()
            .filter_map(|id| cfg.edge(*id))
            .filter(|edge| edge.payload.condition.is_some())
            .collect();
        assert_eq!(edges.len(), 2);
        for edge in edges {
            check_transfer_order(edge.payload, &analysis, &states);
            for (value, taken) in [
                (0, edge.payload.kind == EdgeKind::False),
                (1, edge.payload.kind == EdgeKind::True),
            ] {
                let mut state = ForwardState::boundary();
                let ForwardState::Reached { variables, .. } = &mut state else { panic!("reached") };
                variables.insert(t, field.canonical(value.into()));
                let result = transfer_state(edge.payload.apply(&analysis, &state));
                assert_eq!(result != ForwardState::Unreachable, taken);
            }
        }
    }

    #[test]
    fn linear_constraint_transfer_loses_must_touch_monotonically() {
        let directory = std::env::temp_dir()
            .join(format!("circomspect-phase4-linear-law-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(&source, "template T(){signal input x; var t=0; signal output y; y<==t*x;}")
            .unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("T").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let t = hir.symbols().iter().find(|symbol| symbol.name == "t").unwrap().id;
        let x = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap().id;
        let key = AccessKey { root: x, instance: None, steps: Vec::new() };
        let analysis = ForwardAnalysis::new(&hir, &field);
        let constraint = cfg
            .nodes()
            .iter()
            .find_map(|id| {
                let node = cfg.node(*id)?;
                let CfgNodeKind::Constraint { .. } = &node.kind else { return None };
                Some(node)
            })
            .unwrap();
        let states = variable_states(t, key, &field);
        check_transfer_order(constraint, &analysis, &states);
    }
}
