use std::collections::BTreeSet;
use std::fs;

use abstract_interpretation::graph::FlowGraph;
use parser::hir::{lift_project, ExprId, HirProject, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::build_cfg;
use crate::hir_facts::{
    analyze, AccessKey, AccessKeyStep, Degree, Fact, FactBlocker, FieldContext, IndexKey, Range,
};

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-occurrences-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    fs::create_dir_all(&directory).unwrap();
    let file = directory.join("case.circom");
    fs::write(&file, source).unwrap();
    lift_project(&load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3))))
}

fn expression_at(hir: &HirProject, source: &str, marker: &str) -> ExprId {
    let start = source.find(marker).unwrap();
    hir.expressions()
        .iter()
        .find(|expression| {
            expression.span.start() == start && expression.span.end() == start + marker.len()
        })
        .unwrap()
        .id
}

#[test]
fn shared_loop_expressions_combine_values_and_exact_array_dependencies() {
    let source = "template Check(){signal input a[2];signal output y[2];\
        for(var i=0;i<2;i++){y[i]<==i+a[i];}}";
    let hir = fixture(source).hir;
    let cfg = build_cfg(&hir, hir.definition("Check").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let expression = expression_at(&hir, source, "i+a[i]");
    let start = source.find("i+a[i]").unwrap();
    let induction = hir
        .expressions()
        .iter()
        .find(|expression| expression.span.start() == start && expression.span.end() == start + 1)
        .unwrap()
        .id;
    assert_eq!(facts.range(induction), Fact::known(Range::Canonical));
    assert_eq!(facts.range(expression), Fact::known(Range::Canonical));
    assert_eq!(facts.degree(expression), Fact::known(Degree::Linear));
    assert_eq!(facts.reachable_expression(expression), Fact::known(true));
    let array = hir.symbols().iter().find(|symbol| symbol.name == "a").unwrap().id;
    let mut expected = BTreeSet::new();
    for index in [0, 1] {
        expected.insert(AccessKey {
            root: array,
            instance: None,
            steps: vec![AccessKeyStep::Index(IndexKey::Exact(field.canonical(index.into())))],
        });
    }
    assert_eq!(facts.dependencies(expression), Fact::known(expected));
}

#[test]
fn missing_dead_and_pending_occurrences_keep_distinct_fact_results() {
    let source = "function Other(){return 91;} template Check(){if(0){var dead=7;}var live=3;}";
    let hir = fixture(source).hir;
    let cfg = build_cfg(&hir, hir.definition("Check").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let dead = expression_at(&hir, source, "7");
    let unobserved = expression_at(&hir, source, "91");
    let missing = BTreeSet::from([FactBlocker::MissingExit]);
    assert_eq!(facts.reachable_expression(dead), Fact::known(false));
    assert_eq!(facts.reachable_expression(unobserved), Fact::blocked(missing.clone()));
    for expression in [dead, unobserved] {
        assert_eq!(facts.range(expression), Fact::blocked(missing.clone()));
        assert_eq!(facts.degree(expression), Fact::blocked(missing.clone()));
        assert_eq!(facts.dependencies(expression), Fact::blocked(missing.clone()));
    }
    let live = expression_at(&hir, source, "3");
    let pending = BTreeSet::from([FactBlocker::Budget(cfg.entry())]);
    for budget in [0, 1, 2] {
        let facts = analyze(&hir, &cfg, &field, Some(budget)).unwrap();
        assert_eq!(facts.range(live), Fact::blocked(missing.clone()), "budget {budget}");
        assert_eq!(facts.reachable_expression(live), Fact::blocked(pending.clone()));
        assert_eq!(facts.degree(live), Fact::blocked(pending.clone()));
        assert_eq!(facts.dependencies(live), Fact::blocked(pending.clone()));
    }
}

#[test]
fn foreign_expression_identity_cannot_borrow_local_occurrences() {
    let source = "template Check(){var x=7;}";
    let hir = fixture(source).hir;
    let foreign = fixture(source).hir;
    let cfg = build_cfg(&hir, hir.definition("Check").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let local = expression_at(&hir, source, "7");
    let foreign = expression_at(&foreign, source, "7");
    assert_ne!(local, foreign);
    assert!(!cfg.evaluation_sites(local).is_empty());
    assert!(cfg.evaluation_sites(foreign).is_empty());
    assert_eq!(facts.range(local), Fact::known(Range::Exact(field.canonical(7.into()))));
    assert_eq!(
        facts.reachable_expression(foreign),
        Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery,]))
    );
    let opaque = BTreeSet::from([FactBlocker::OpaqueExpression(foreign)]);
    assert_eq!(facts.range(foreign), Fact::blocked(opaque.clone()));
    assert_eq!(facts.degree(foreign), Fact::blocked(opaque.clone()));
    assert_eq!(facts.dependencies(foreign), Fact::blocked(opaque));
}

fn compare_occurrence_index(hir: &HirProject, cfg: &crate::hir_cfg::DefinitionCfg) {
    for expression in hir.expressions() {
        let mut expected = Vec::new();
        for id in cfg.nodes() {
            if let crate::hir_cfg::CfgNodeKind::Evaluate(evaluated) = cfg.node(*id).unwrap().kind {
                if evaluated == expression.id {
                    expected.push(*id);
                }
            }
        }
        assert_eq!(cfg.evaluation_sites(expression.id), expected);
    }
}

#[test]
fn occurrence_slices_belong_to_each_ordinary_or_specialized_cfg() {
    use crate::interprocedural::{CallOwner, CallReachability, ProjectAnalysis};

    let source = "template Check(n){signal output y[n];\
        for(var i=0;i<n;i++){y[i]<==i+9;}}component main=Check(2);";
    let project = fixture(source);
    let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &project.hir)
    else {
        panic!("main must be reachable");
    };
    let evidence = provider.main_evidence(&call).unwrap();
    let cfg = build_cfg(&project.hir, evidence.context().definition()).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    compare_occurrence_index(&project.hir, &cfg);
    compare_occurrence_index(&project.hir, facts.cfg());
    let expression = expression_at(&project.hir, source, "i+9");
    assert_eq!(cfg.evaluation_sites(expression).len(), 1);
    assert_eq!(facts.cfg().evaluation_sites(expression).len(), 2);
    assert_eq!(facts.range(expression), Fact::known(Range::Canonical));
}
