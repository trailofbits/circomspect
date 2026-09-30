use std::collections::{BTreeMap, BTreeSet};
use std::cmp::Ordering;

use abstract_interpretation::graph::NodeId;
use abstract_interpretation::lattice::Lattice;
use abstract_interpretation::solver::{DataflowAnalysis, Transfer, TransferOutcome};
use parser::hir::{AccessPath, ExprId, ExprKind, HirProject, SymbolId, SymbolKind};
use parser::new_frontend::{BinaryOperator, PostfixOperator, UnaryOperator};

use crate::hir_cfg::{CfgEdge, CfgNode, CfgNodeKind, DefinitionCfg, EdgeKind};

use super::access::{key_for_path, AccessKey, MayAccessSet};
use super::domains::DegreeUpper;
use super::field::{FieldContext, FieldValue};
use super::walk::VisitDefiniteAccesses;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ForwardState {
    Unreachable,
    Reached {
        variables: BTreeMap<SymbolId, FieldValue>,
        dependencies: BTreeMap<SymbolId, MayAccessSet>,
        degrees: BTreeMap<SymbolId, DegreeUpper>,
        may_constraints: BTreeSet<NodeId>,
        must_constraints: BTreeSet<NodeId>,
        must_touches: BTreeSet<AccessKey>,
        must_fixed: BTreeSet<(AccessKey, FieldValue)>,
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
            dependencies: BTreeMap::new(),
            degrees: BTreeMap::new(),
            may_constraints: BTreeSet::new(),
            must_constraints: BTreeSet::new(),
            must_touches: BTreeSet::new(),
            must_fixed: BTreeSet::new(),
        }
    }

    pub fn variables(&self) -> Option<&BTreeMap<SymbolId, FieldValue>> {
        let Self::Reached { variables, .. } = self else { return None };
        Some(variables)
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
                    dependencies: left_dependencies,
                    degrees: left_degrees,
                    may_constraints: left_may,
                    must_constraints: left_must,
                    must_touches: left_touches,
                    must_fixed: left_fixed,
                },
                Self::Reached {
                    variables: right,
                    dependencies: right_dependencies,
                    degrees: right_degrees,
                    may_constraints: right_may,
                    must_constraints: right_must,
                    must_touches: right_touches,
                    must_fixed: right_fixed,
                },
            ) => {
                right.iter().all(|(key, value)| left.get(key) == Some(value))
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
                dependencies: left_dependencies,
                degrees: left_degrees,
                may_constraints: left_may,
                must_constraints: left_must,
                must_touches: left_touches,
                must_fixed: left_fixed,
            },
            Self::Reached {
                variables: right,
                dependencies: right_dependencies,
                degrees: right_degrees,
                may_constraints: right_may,
                must_constraints: right_must,
                must_touches: right_touches,
                must_fixed: right_fixed,
            },
        ) = (&mut *self, other)
        else {
            return false;
        };
        left.retain(|key, value| right.get(key) == Some(value));
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
        *self != old
    }
}

pub struct ForwardAnalysis<'a> {
    pub hir: &'a HirProject,
    pub field: &'a FieldContext,
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
    let value = eval_expression(analysis.hir, analysis.field, value, variables)?;
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
        let value = eval_expression(analysis.hir, analysis.field, left, variables)?;
        return Some((key, value));
    }
    let right = right?;
    fixed_side(analysis, left, right, variables)
        .or_else(|| fixed_side(analysis, right, left, variables))
}

fn constraint_touches(
    analysis: &ForwardAnalysis<'_>,
    kind: &CfgNodeKind,
    values: &BTreeMap<SymbolId, FieldValue>,
) -> BTreeSet<AccessKey> {
    let CfgNodeKind::Constraint { target, left, right } = kind else { return BTreeSet::new() };
    let mut touched = BTreeSet::new();
    if let Some(path) = target {
        let key = key_for_path(analysis.hir, analysis.field, path, values);
        if key.exact_alias(&key) {
            touched.insert(key);
        }
    }
    for expression in [Some(*left), *right].into_iter().flatten() {
        expression.visit_definite_accesses(analysis.hir, &mut |path| {
            if analysis
                .hir
                .symbol(path.root)
                .is_some_and(|symbol| symbol.kind == SymbolKind::Variable)
            {
                return;
            }
            let key = key_for_path(analysis.hir, analysis.field, path, values);
            if key.exact_alias(&key) {
                touched.insert(key);
            }
        });
    }
    touched
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
            let arms = if let Some(value) =
                eval_expression(analysis.hir, analysis.field, *condition, values)
            {
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
        ExprKind::Call { .. } | ExprKind::AnonymousComponent { .. } | ExprKind::Opaque(_) => None,
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
        ExprKind::Unary { .. } => DegreeUpper::Unbounded,
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
            if let Some(value) = eval_expression(analysis.hir, analysis.field, *condition, values) {
                let selected = if analysis.field.is_zero(&value) { no } else { yes };
                expression_degree(analysis, *selected, values, degrees)
            } else {
                expression_degree(analysis, *yes, values, degrees)
                    .max(expression_degree(analysis, *no, values, degrees))
            }
        }
        ExprKind::Call { .. }
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
    let value = if target.steps.is_empty() {
        eval_expression(analysis.hir, analysis.field, value, variables)
    } else {
        None
    };
    if let Some(value) = value {
        variables.insert(target.root, value);
    } else {
        variables.remove(&target.root);
    }
}

impl DataflowAnalysis<DefinitionCfg> for ForwardAnalysis<'_> {
    type State = ForwardState;
    type Reason = String;

    fn boundary(&self, _: NodeId) -> Self::State {
        ForwardState::boundary()
    }
}

impl Transfer<ForwardAnalysis<'_>, ForwardState, String> for CfgNode {
    fn apply(
        &self,
        analysis: &ForwardAnalysis<'_>,
        input: &ForwardState,
    ) -> TransferOutcome<ForwardState, String> {
        let mut output = input.clone();
        let ForwardState::Reached {
            variables,
            dependencies,
            degrees,
            may_constraints,
            must_constraints,
            must_touches,
            must_fixed,
        } = &mut output
        else {
            return TransferOutcome::Known(output);
        };
        match &self.kind {
            CfgNodeKind::Evaluate(id) => {
                let Some(expression) = analysis.hir.expression(*id) else {
                    return TransferOutcome::Opaque {
                        provisional: output,
                        reason: "missing expression".into(),
                    };
                };
                if let ExprKind::Opaque(reason) = &expression.kind {
                    return TransferOutcome::Opaque {
                        provisional: output,
                        reason: format!("{reason:?}"),
                    };
                }
                if let ExprKind::AnonymousComponent { .. } = &expression.kind {
                    return TransferOutcome::Opaque {
                        provisional: output,
                        reason: "external component summary".into(),
                    };
                }
            }
            CfgNodeKind::Assignment { target, value } => {
                if analysis
                    .hir
                    .symbol(target.root)
                    .is_some_and(|symbol| symbol.kind == SymbolKind::Variable)
                {
                    assign_degree(analysis, target, *value, variables, degrees);
                    assign_dependencies(analysis, target, *value, variables, dependencies);
                    assign_value(analysis, target, *value, variables);
                }
            }
            CfgNodeKind::Update { target, operator } => {
                if let Err(reason) = apply_update(analysis, target, *operator, variables) {
                    return TransferOutcome::Opaque { provisional: output, reason: reason.into() };
                }
                degrees.insert(target.root, DegreeUpper::Constant);
            }
            CfgNodeKind::Constraint { target, left, right } => {
                may_constraints.insert(self.id);
                must_constraints.insert(self.id);
                must_touches.extend(constraint_touches(analysis, &self.kind, variables));
                if let Some((key, value)) =
                    fixed_equation(analysis, target.as_ref(), *left, *right, variables)
                {
                    must_fixed.insert((key, value));
                }
            }
            CfgNodeKind::Opaque(reason) => {
                return TransferOutcome::Opaque {
                    provisional: output,
                    reason: format!("{reason:?}"),
                };
            }
            CfgNodeKind::Instantiate { .. } => {
                return TransferOutcome::Opaque {
                    provisional: output,
                    reason: "external component summary".into(),
                };
            }
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::LoopHeader
            | CfgNodeKind::Branch { .. }
            | CfgNodeKind::Witness { .. }
            | CfgNodeKind::Declaration
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Assert { .. }
            | CfgNodeKind::Log => {}
        }
        TransferOutcome::Known(output)
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
        let Some(value) = eval_expression(analysis.hir, analysis.field, condition, variables)
        else {
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
    let expression = hir.expression(id)?;
    match &expression.kind {
        ExprKind::Number(text) => field.parse(text),
        ExprKind::Access(path) if path.steps.is_empty() => variables.get(&path.root).cloned(),
        ExprKind::Unary { operator, operand } => {
            let value = eval_expression(hir, field, *operand, variables)?;
            match operator {
                UnaryOperator::Negate => Some(field.negate(&value)),
                UnaryOperator::BooleanNot => {
                    Some(field.canonical(i32::from(field.is_zero(&value)).into()))
                }
                UnaryOperator::Complement => None,
            }
        }
        ExprKind::Binary { operator, left, right } => {
            let left = eval_expression(hir, field, *left, variables)?;
            let right = eval_expression(hir, field, *right, variables)?;
            match operator {
                BinaryOperator::Add => Some(field.add(&left, &right)),
                BinaryOperator::Subtract => Some(field.subtract(&left, &right)),
                BinaryOperator::Multiply => Some(field.multiply(&left, &right)),
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
                _ => None,
            }
        }
        ExprKind::Ternary { condition, yes, no } => {
            let condition = eval_expression(hir, field, *condition, variables)?;
            let selected = if field.is_zero(&condition) { no } else { yes };
            eval_expression(hir, field, *selected, variables)
        }
        ExprKind::Parallel(operand) => eval_expression(hir, field, *operand, variables),
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
    use parser::hir::lower_project;
    use parser::new_frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;
    use std::fs;

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
        let hir = lower_project(&loaded).hir;
        let definition = hir.definition("Check").unwrap();
        let cfg = crate::hir_cfg::build_cfg(&hir, definition).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let SolveResult::Complete(states) =
            solve::<_, _, Forward>(&cfg, &ForwardAnalysis { hir: &hir, field: &field }, None)
                .unwrap()
        else {
            panic!("complete local solver")
        };
        let x = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap().id;
        states.get(&cfg.exit)?.output.as_ref()?.variables()?.get(&x).cloned()
    }

    #[test]
    fn late_predecessor_requeues_the_real_hir_join() {
        let one = FieldContext::for_curve(Curve::Bn254).canonical(1.into());
        assert_eq!(exit_value("1"), Some(one));
        assert_eq!(exit_value("2"), None);
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
            let hir = lower_project(&loaded).hir;
            let definition = hir.definition("Check").unwrap();
            let cfg = crate::hir_cfg::build_cfg(&hir, definition).unwrap();
            let field = FieldContext::for_curve(Curve::Bn254);
            let SolveResult::Complete(states) =
                solve::<_, _, Forward>(&cfg, &ForwardAnalysis { hir: &hir, field: &field }, None)
                    .unwrap()
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
            let state = states.get(&cfg.exit)?.output.as_ref()?;
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
        let hir = lower_project(&loaded).hir;
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
        let analysis = ForwardAnalysis { hir: &hir, field: &field };
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
                    dependencies: BTreeMap::new(),
                    degrees: BTreeMap::new(),
                    may_constraints,
                    must_constraints,
                    must_touches: BTreeSet::new(),
                    must_fixed: BTreeSet::new(),
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
        let hir = lower_project(&loaded).hir;
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
        let analysis = ForwardAnalysis { hir: &hir, field: &field };
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
            "template T(){signal input x; var t=x; t++; signal output y; \
             y<==t; if(1){y===1;}else{y===2;}}",
        )
        .unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lower_project(&loaded).hir;
        let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("T").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let t = hir.symbols().iter().find(|symbol| symbol.name == "t").unwrap().id;
        let x = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap().id;
        let key = AccessKey { root: x, instance: None, steps: Vec::new() };
        let states = variable_states(t, key, &field);
        let analysis = ForwardAnalysis { hir: &hir, field: &field };
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
        let hir = lower_project(&loaded).hir;
        let cfg = crate::hir_cfg::build_cfg(&hir, hir.definition("T").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let t = hir.symbols().iter().find(|symbol| symbol.name == "t").unwrap().id;
        let key = AccessKey { root: t, instance: None, steps: Vec::new() };
        let states = variable_states(t, key, &field);
        let analysis = ForwardAnalysis { hir: &hir, field: &field };
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
}
