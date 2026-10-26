use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::sync::Arc;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use abstract_interpretation::lattice::Lattice;
use abstract_interpretation::solver::{Transfer, TransferOutcome};
use parser::hir::{lift_project, ExprKind, HirProject, SymbolId};
use parser::frontend::{load_sources, AssignmentOperator, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::{build_cfg, CfgNode, CfgNodeKind, DefinitionCfg};
use crate::hir_facts::access::{AccessKey, AccessKeyStep, IndexKey, MayAccessSet};
use crate::hir_facts::domains::DegreeUpper;
use crate::hir_facts::forward::{ForwardAnalysis, ForwardState, LocalValueFacts, ReachedFacts};
use crate::hir_facts::relations::{
    variable_polynomial, ExpressionPolynomial, MustEquations, MustSymbolicVariables,
    NormalizationInputs,
};
use crate::hir_facts::FieldContext;

const SOURCE: &str = "template T(n){signal input a[2];var x=n;x*=2;x++;x=a[x];\
    a[0]===1;a[1]===a[0]*a[0]*a[0];}";

fn fixture(source: &str) -> (HirProject, DefinitionCfg, FieldContext) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-forward-state-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    fs::create_dir_all(&directory).unwrap();
    let file = directory.join("case.circom");
    fs::write(&file, source).unwrap();
    let hir = lift_project(&load_sources(
        &[file],
        &[directory],
        VersionPolicy::new(Version::new(2, 2, 3)),
    ))
    .hir;
    let cfg = build_cfg(&hir, hir.definition("T").unwrap()).unwrap();
    (hir, cfg, FieldContext::for_curve(Curve::Bn254))
}

fn symbol(hir: &HirProject, name: &str) -> SymbolId {
    hir.symbols().iter().find(|symbol| symbol.name == name).unwrap().id
}

fn signal_key(hir: &HirProject, field: &FieldContext, index: i32) -> AccessKey {
    AccessKey {
        root: symbol(hir, "a"),
        instance: None,
        steps: vec![AccessKeyStep::Index(IndexKey::Exact(field.canonical(index.into())))],
    }
}

fn seeded_state(hir: &HirProject, cfg: &DefinitionCfg, field: &FieldContext) -> ForwardState {
    let x = symbol(hir, "x");
    let one = field.canonical(1.into());
    let mut state = ForwardState::with_scalar_parameters(&BTreeMap::from([(x, one.clone())]));
    let ForwardState::Reached(ReachedFacts {
        locals: LocalValueFacts { symbolic, dependencies, degrees, .. },
        ..
    }) = &mut state
    else {
        panic!("reached boundary")
    };
    Arc::make_mut(symbolic).insert(x, ExpressionPolynomial::constant(field, one));
    dependencies.insert(x, MayAccessSet::from_keys(BTreeSet::from([signal_key(hir, field, 0)])));
    degrees.insert(x, DegreeUpper::Linear);
    let analysis = ForwardAnalysis::new(hir, field);
    for id in cfg.nodes() {
        let node = cfg.node(*id).unwrap();
        let CfgNodeKind::Constraint(_) = &node.kind else { continue };
        let TransferOutcome::Known(output) = node.apply(&analysis, &state) else {
            panic!("constraint transfer")
        };
        state = output;
    }
    assert_eq!(state.constraints().unwrap().0.len(), 2);
    assert_eq!(state.fixed_equations().unwrap().len(), 1);
    state
}

fn assert_opaque(
    node: &CfgNode,
    analysis: &ForwardAnalysis<'_>,
    input: &ForwardState,
    expected: &ForwardState,
    reason: &str,
) {
    let TransferOutcome::Opaque { provisional, reason: actual } = node.apply(analysis, input)
    else {
        panic!("expected opaque transfer")
    };
    assert_eq!(actual, reason);
    assert_eq!(&provisional, expected);
}

#[test]
fn failed_deferred_shape_preserves_every_fact_except_target_symbolic_value() {
    let (hir, cfg, field) = fixture(SOURCE);
    let node = cfg
        .nodes()
        .iter()
        .find_map(|id| {
            let node = cfg.node(*id)?;
            let CfgNodeKind::DeferredAssignment { .. } = &node.kind else { return None };
            Some(node)
        })
        .unwrap();
    let input = seeded_state(&hir, &cfg, &field);
    let snapshot = input.clone();
    let mut expected = input.clone();
    let ForwardState::Reached(ReachedFacts { locals: LocalValueFacts { symbolic, .. }, .. }) =
        &mut expected
    else {
        panic!("reached")
    };
    Arc::make_mut(symbolic).remove(symbol(&hir, "x"));
    assert_opaque(
        node,
        &ForwardAnalysis::new(&hir, &field),
        &input,
        &expected,
        "deferred assignment shape",
    );
    assert_eq!(input, snapshot);
}

#[test]
fn unsupported_compound_transfers_forget_local_properties_and_keep_constraints() {
    let (hir, cfg, field) = fixture(SOURCE);
    let mut nodes = Vec::new();
    for id in cfg.nodes() {
        let node = cfg.node(*id).unwrap();
        if let CfgNodeKind::Assignment { operator: AssignmentOperator::Multiply, .. } = &node.kind {
            nodes.push(node.clone());
        }
        if let CfgNodeKind::DeferredAssignment { target, value, .. } = &node.kind {
            let mut deferred = node.clone();
            deferred.kind = CfgNodeKind::DeferredAssignment {
                target: target.clone(),
                value: *value,
                operator: AssignmentOperator::Multiply,
            };
            nodes.push(deferred);
        }
    }
    assert_eq!(nodes.len(), 2);
    let input = seeded_state(&hir, &cfg, &field);
    let mut expected = input.clone();
    let ForwardState::Reached(ReachedFacts {
        locals: LocalValueFacts { variables, symbolic, dependencies, degrees, .. },
        ..
    }) = &mut expected
    else {
        panic!("reached")
    };
    let x = symbol(&hir, "x");
    variables.remove(&x);
    Arc::make_mut(symbolic).remove(x);
    dependencies.remove(&x);
    degrees.remove(&x);
    for node in nodes {
        assert_opaque(
            &node,
            &ForwardAnalysis::new(&hir, &field),
            &input,
            &expected,
            "unsupported compound assignment Multiply",
        );
    }
}

#[test]
fn failed_postfix_update_preserves_dependencies_degrees_and_constraints() {
    let (hir, cfg, field) = fixture(SOURCE);
    let node = cfg
        .nodes()
        .iter()
        .find_map(|id| {
            let node = cfg.node(*id)?;
            let CfgNodeKind::Update { .. } = &node.kind else { return None };
            Some(node)
        })
        .unwrap();
    let mut input = seeded_state(&hir, &cfg, &field);
    let x = symbol(&hir, "x");
    let ForwardState::Reached(ReachedFacts { locals: LocalValueFacts { variables, .. }, .. }) =
        &mut input
    else {
        panic!("reached")
    };
    variables.remove(&x);
    let mut expected = input.clone();
    let ForwardState::Reached(ReachedFacts { locals: LocalValueFacts { symbolic, .. }, .. }) =
        &mut expected
    else {
        panic!("reached")
    };
    Arc::make_mut(symbolic).remove(x);
    assert_opaque(
        node,
        &ForwardAnalysis::new(&hir, &field),
        &input,
        &expected,
        "unknown update value",
    );
}

#[test]
fn self_indexed_assignment_uses_old_values_and_keeps_independent_properties() {
    let (hir, cfg, field) = fixture(
        "template T(){signal input a[2];var x=1;x=a[x];a[0]===1;\
        a[1]===a[0]*a[0]*a[0];}",
    );
    let (node, expression) = cfg
        .nodes()
        .iter()
        .find_map(|id| {
            let node = cfg.node(*id)?;
            let CfgNodeKind::Assignment { value, operator: AssignmentOperator::Assign, .. } =
                &node.kind
            else {
                return None;
            };
            let ExprKind::Access(_) = &hir.expression(*value)?.kind else { return None };
            Some((node, *value))
        })
        .unwrap();
    let x = symbol(&hir, "x");
    let mut input = seeded_state(&hir, &cfg, &field);
    let ForwardState::Reached(ReachedFacts {
        locals: LocalValueFacts { dependencies, .. }, ..
    }) = &mut input
    else {
        panic!("reached")
    };
    dependencies.insert(x, MayAccessSet::default());
    let inputs = NormalizationInputs::new(
        &hir,
        &field,
        input.variables().unwrap(),
        None,
        input.symbolic().unwrap(),
    );
    let polynomial = variable_polynomial(&inputs, expression).unwrap();
    let mut expected = input.clone();
    let ForwardState::Reached(ReachedFacts {
        locals: LocalValueFacts { variables, symbolic, dependencies, degrees, .. },
        ..
    }) = &mut expected
    else {
        panic!("reached")
    };
    variables.remove(&x);
    Arc::make_mut(symbolic).insert(x, polynomial);
    dependencies.insert(x, MayAccessSet::from_keys(BTreeSet::from([signal_key(&hir, &field, 1)])));
    degrees.insert(x, DegreeUpper::Linear);
    let snapshot = input.clone();
    let TransferOutcome::Known(output) = node.apply(&ForwardAnalysis::new(&hir, &field), &input)
    else {
        panic!("known indexed assignment")
    };
    assert_eq!(output, expected);
    assert_eq!(input, snapshot);
}

#[test]
fn self_conditioned_assignment_selects_old_rhs_degree_and_dependencies() {
    let (hir, cfg, field) = fixture(
        "template T(){signal input a[2];var x=1;x=x?a[0]:a[1]*a[1];a[0]===1;\
         a[1]===a[0]*a[0]*a[0];}",
    );
    let node = cfg
        .nodes()
        .iter()
        .find_map(|id| {
            let node = cfg.node(*id)?;
            let CfgNodeKind::Assignment { value, .. } = &node.kind else { return None };
            let ExprKind::Ternary { .. } = &hir.expression(*value)?.kind else { return None };
            Some(node)
        })
        .unwrap();
    let input = seeded_state(&hir, &cfg, &field);
    let mut expected = input.clone();
    let ForwardState::Reached(ReachedFacts {
        locals: LocalValueFacts { variables, symbolic, .. },
        ..
    }) = &mut expected
    else {
        panic!("reached")
    };
    let x = symbol(&hir, "x");
    variables.remove(&x);
    Arc::make_mut(symbolic).remove(x);
    let TransferOutcome::Known(output) = node.apply(&ForwardAnalysis::new(&hir, &field), &input)
    else {
        panic!("known conditional assignment")
    };
    assert_eq!(output, expected);
}

fn altered(state: &ForwardState, change: impl FnOnce(&mut ReachedFacts)) -> ForwardState {
    let mut state = state.clone();
    let ForwardState::Reached(facts) = &mut state else { panic!("reached fixture") };
    change(facts);
    state
}

fn assert_join(left: &ForwardState, right: &ForwardState, expected: &ForwardState) {
    let left_snapshot = left.clone();
    let right_snapshot = right.clone();
    let mut joined = left.clone();
    let changed = joined.join_assign(right);
    assert_eq!(&joined, expected);
    assert_eq!(changed, joined != *left);
    assert!(!joined.join_assign(right));
    assert_eq!(&joined, expected);
    assert_eq!(left, &left_snapshot);
    assert_eq!(right, &right_snapshot);
}

#[test]
fn local_join_reports_every_property_change_with_exact_results() {
    let (hir, cfg, field) = fixture(SOURCE);
    let left = seeded_state(&hir, &cfg, &field);
    let x = symbol(&hir, "x");
    let left = altered(&left, |facts| {
        facts.locals.degrees.insert(x, DegreeUpper::Constant);
    });
    let mut wildcard = signal_key(&hir, &field, 0);
    wildcard.steps = vec![AccessKeyStep::Index(IndexKey::Unknown)];
    let right_states = [
        altered(&left, |facts| {
            facts.locals.variables.remove(&x);
        }),
        altered(&left, |facts| {
            Arc::make_mut(&mut facts.locals.symbolic).remove(x);
        }),
        altered(&left, |facts| {
            facts.locals.dependencies.remove(&x);
        }),
        altered(&left, |facts| {
            facts
                .locals
                .dependencies
                .insert(x, MayAccessSet::from_keys(BTreeSet::from([wildcard])));
        }),
        altered(&left, |facts| {
            facts.locals.degrees.remove(&x);
        }),
        altered(&left, |facts| {
            facts.locals.degrees.insert(x, DegreeUpper::Linear);
        }),
    ];
    for right in right_states {
        assert_ne!(left, right);
        assert_join(&left, &right, &right);
    }
    let right = altered(&left, |facts| {
        facts.locals.variables.insert(x, field.canonical(2.into()));
    });
    let expected = altered(&left, |facts| {
        facts.locals.variables.remove(&x);
    });
    assert_join(&left, &right, &expected);
    let right = altered(&left, |facts| {
        facts.locals.degrees.insert(x, DegreeUpper::Unbounded);
    });
    let expected = altered(&left, |facts| {
        facts.locals.degrees.remove(&x);
    });
    assert_join(&left, &right, &expected);
}

#[test]
fn constraint_join_reports_each_set_and_provenance_change() {
    let (hir, cfg, field) = fixture(SOURCE);
    let left = seeded_state(&hir, &cfg, &field);
    let new_site = NodeId::new(999);
    let right_states = [
        altered(&left, |facts| {
            facts.constraints.may_constraints.insert(new_site);
        }),
        altered(&left, |facts| {
            facts.constraints.must_constraints.clear();
        }),
        altered(&left, |facts| {
            facts.constraints.must_touches.clear();
        }),
        altered(&left, |facts| {
            facts.constraints.must_fixed.clear();
        }),
        altered(&left, |facts| {
            let MustEquations::Reached { equations, .. } =
                Arc::make_mut(&mut facts.constraints.must_equations)
            else {
                panic!("reached")
            };
            assert_eq!(equations.len(), 1);
            for origins in equations.values_mut() {
                origins.insert(new_site);
            }
        }),
        altered(&left, |facts| {
            Arc::make_mut(&mut facts.constraints.must_equations).block(new_site);
        }),
        altered(&left, |facts| {
            let MustEquations::Reached { equations, .. } =
                Arc::make_mut(&mut facts.constraints.must_equations)
            else {
                panic!("reached")
            };
            equations.clear();
        }),
    ];
    for right in right_states {
        assert_ne!(left, right);
        assert_join(&left, &right, &right);
    }
}

#[test]
fn join_keeps_later_changes_and_distinguishes_bottom_from_reached_empty() {
    let (hir, cfg, field) = fixture(SOURCE);
    let left = seeded_state(&hir, &cfg, &field);
    let right = altered(&left, |facts| {
        facts.locals.variables.clear();
        facts.locals.symbolic = Arc::new(MustSymbolicVariables::reachable_empty());
        facts.locals.dependencies.clear();
        facts.locals.degrees.clear();
        facts.constraints.may_constraints.insert(NodeId::new(999));
        facts.constraints.must_constraints.clear();
        facts.constraints.must_touches.clear();
        facts.constraints.must_fixed.clear();
        facts.constraints.must_equations = Arc::new(MustEquations::reachable_empty());
    });
    let expected = altered(&right, |facts| {
        let MustEquations::Reached { blockers, .. } = left.must_equations() else {
            panic!("reached equations")
        };
        for blocker in blockers {
            Arc::make_mut(&mut facts.constraints.must_equations).block(*blocker);
        }
    });
    assert_join(&left, &right, &expected);
    for state in [ForwardState::Unreachable, ForwardState::boundary(), left, right] {
        assert_join(&ForwardState::Unreachable, &state, &state);
        assert_join(&state, &ForwardState::Unreachable, &state);
        assert_join(&state, &state, &state);
    }
}
