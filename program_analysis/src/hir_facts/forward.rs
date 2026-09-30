use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::NodeId;
use abstract_interpretation::lattice::Lattice;
use abstract_interpretation::solver::{DataflowAnalysis, Transfer, TransferOutcome};
use parser::hir::{AccessPath, ExprId, ExprKind, HirProject, SymbolId, SymbolKind};
use parser::new_frontend::{BinaryOperator, PostfixOperator, UnaryOperator};

use crate::hir_cfg::{CfgEdge, CfgNode, CfgNodeKind, DefinitionCfg, EdgeKind};

use super::access::{key_for_path, AccessKey};
use super::field::{FieldContext, FieldValue};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ForwardState {
    Unreachable,
    Reached {
        variables: BTreeMap<SymbolId, FieldValue>,
        may_constraints: BTreeSet<NodeId>,
        must_constraints: BTreeSet<NodeId>,
        must_fixed: BTreeMap<AccessKey, Option<FieldValue>>,
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
            may_constraints: BTreeSet::new(),
            must_constraints: BTreeSet::new(),
            must_fixed: BTreeMap::new(),
        }
    }

    pub fn variables(&self) -> Option<&BTreeMap<SymbolId, FieldValue>> {
        let Self::Reached { variables, .. } = self else { return None };
        Some(variables)
    }

    pub fn constraints(&self) -> Option<(&BTreeSet<NodeId>, &BTreeSet<NodeId>)> {
        let Self::Reached { may_constraints, must_constraints, .. } = self else { return None };
        Some((may_constraints, must_constraints))
    }

    pub fn fixed_values(&self) -> Option<&BTreeMap<AccessKey, Option<FieldValue>>> {
        let Self::Reached { must_fixed, .. } = self else { return None };
        Some(must_fixed)
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
                    may_constraints: left_may,
                    must_constraints: left_must,
                    must_fixed: left_fixed,
                },
                Self::Reached {
                    variables: right,
                    may_constraints: right_may,
                    must_constraints: right_must,
                    must_fixed: right_fixed,
                },
            ) => {
                right.iter().all(|(key, value)| left.get(key) == Some(value))
                    && left_may.is_subset(right_may)
                    && left_must.is_superset(right_must)
                    && right_fixed.iter().all(|(key, value)| match (left_fixed.get(key), value) {
                        (Some(Some(left)), Some(right)) => left == right,
                        (Some(_), None) => true,
                        _ => false,
                    })
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
                may_constraints: left_may,
                must_constraints: left_must,
                must_fixed: left_fixed,
            },
            Self::Reached {
                variables: right,
                may_constraints: right_may,
                must_constraints: right_must,
                must_fixed: right_fixed,
            },
        ) = (&mut *self, other)
        else {
            return false;
        };
        left.retain(|key, value| right.get(key) == Some(value));
        left_may.extend(right_may);
        left_must.retain(|site| right_must.contains(site));
        left_fixed.retain(|key, value| {
            let Some(right) = right_fixed.get(key) else { return false };
            if value != right {
                *value = None;
            }
            true
        });
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
        let ForwardState::Reached { variables, may_constraints, must_constraints, must_fixed } =
            &mut output
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
                    let value = if target.steps.is_empty() {
                        eval_expression(analysis.hir, analysis.field, *value, variables)
                    } else {
                        None
                    };
                    if let Some(value) = value {
                        variables.insert(target.root, value);
                    } else {
                        variables.remove(&target.root);
                    }
                }
            }
            CfgNodeKind::Update { target, operator } => {
                if let Err(reason) = apply_update(analysis, target, *operator, variables) {
                    return TransferOutcome::Opaque { provisional: output, reason: reason.into() };
                }
            }
            CfgNodeKind::Constraint { target, left, right } => {
                may_constraints.insert(self.id);
                must_constraints.insert(self.id);
                if let Some((key, value)) =
                    fixed_equation(analysis, target.as_ref(), *left, *right, variables)
                {
                    match must_fixed.entry(key) {
                        std::collections::btree_map::Entry::Vacant(entry) => {
                            entry.insert(Some(value));
                        }
                        std::collections::btree_map::Entry::Occupied(mut entry) => {
                            if entry.get() != &Some(value) {
                                entry.insert(None);
                            }
                        }
                    }
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
                BinaryOperator::Less => Some(field.canonical(i32::from(left < right).into())),
                BinaryOperator::LessEqual => Some(field.canonical(i32::from(left <= right).into())),
                BinaryOperator::Greater => Some(field.canonical(i32::from(left > right).into())),
                BinaryOperator::GreaterEqual => {
                    Some(field.canonical(i32::from(left >= right).into()))
                }
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
            states.get(&cfg.exit)?.output.as_ref()?.fixed_values()?.get(&key).cloned().flatten()
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
        fs::write(&source, "template T(){signal input x;}").unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lower_project(&loaded).hir;
        let root = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap().id;
        let key = AccessKey { root, instance: None, steps: Vec::new() };
        let field = FieldContext::for_curve(Curve::Bn254);
        let fixed = [Some(field.canonical(1.into())), Some(field.canonical(2.into())), None];
        let mut states = vec![ForwardState::Unreachable, ForwardState::boundary()];
        for value in fixed {
            let mut state = ForwardState::boundary();
            let ForwardState::Reached { must_fixed, .. } = &mut state else { panic!("reached") };
            must_fixed.insert(key.clone(), value);
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
                    may_constraints,
                    must_constraints,
                    must_fixed: BTreeMap::new(),
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
}
