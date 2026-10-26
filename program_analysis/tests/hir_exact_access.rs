// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::assert_is_empty,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use std::fs;

use abstract_interpretation::graph::FlowGraph;
use circomspect_program_analysis::hir_cfg::{build_cfg, CfgNodeKind};
use circomspect_program_analysis::hir_facts::{analyze, AccessKeyStep, FieldContext, IndexKey};
use parser::hir::{lift_project, AccessPath, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-exact-access-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty());
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    lifted
}

fn witnesses(cfg: &circomspect_program_analysis::hir_cfg::DefinitionCfg) -> Vec<AccessPath> {
    let mut paths = Vec::new();
    for id in cfg.nodes() {
        if let CfgNodeKind::Witness { target, .. } = &cfg.node(*id).unwrap().kind {
            paths.push(target.clone());
        }
    }
    paths
}

#[test]
fn literal_spellings_and_proved_indices_share_an_exact_key() {
    let lifted = fixture("template T(){signal a[2];var i=1;a[1]<--1;a[0x1]<--1;a[i]<--1;}");
    let cfg = build_cfg(&lifted.hir, lifted.hir.definition("T").unwrap()).unwrap();
    let paths = witnesses(&cfg);
    for curve in [Curve::Bn254, Curve::Bls12_381, Curve::Goldilocks] {
        let field = FieldContext::for_curve(curve);
        let facts = analyze(&lifted.hir, &cfg, &field, None).unwrap();
        let keys: Vec<_> = paths.iter().map(|path| facts.exact_access_key(path)).collect();
        let first = keys[0].certified().unwrap();
        assert_eq!(first.steps, [AccessKeyStep::Index(IndexKey::Exact(field.canonical(1.into())))]);
        assert!(first.exact_alias(first));
        for key in &keys {
            assert_eq!(key.certified(), Some(first));
        }
    }
}

#[test]
fn foreign_source_paths_and_partial_aggregates_cannot_be_certified() {
    let lifted = fixture("template T(){signal a[2];a[0]<--1;} template U(){signal a;a<--1;}");
    let foreign = fixture("template T(){signal a[2];a[0]<--1;}");
    let cfg = build_cfg(&lifted.hir, lifted.hir.definition("T").unwrap()).unwrap();
    let other = build_cfg(&lifted.hir, lifted.hir.definition("U").unwrap()).unwrap();
    let foreign_cfg = build_cfg(&foreign.hir, foreign.hir.definition("T").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&lifted.hir, &cfg, &field, None).unwrap();
    assert!(facts.exact_access_key(&witnesses(&other)[0]).certified().is_none());
    assert!(facts.exact_access_key(&witnesses(&foreign_cfg)[0]).certified().is_none());
    let mut aggregate = witnesses(&cfg)[0].clone();
    aggregate.steps.clear();
    assert!(facts.exact_access_key(&aggregate).certified().is_none());
}

#[test]
fn out_of_bounds_and_field_reduced_literal_indices_do_not_alias_valid_elements() {
    for index in ["2", "18446744069414584321"] {
        let lifted = fixture(&format!("template T(){{signal a[2];a[{index}]<--1;}}"));
        let cfg = build_cfg(&lifted.hir, lifted.hir.definition("T").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Goldilocks);
        let facts = analyze(&lifted.hir, &cfg, &field, None).unwrap();
        assert!(facts.exact_access_key(&witnesses(&cfg)[0]).certified().is_none());
    }
}

#[test]
fn symbolic_indices_and_provisional_loop_values_never_get_exact_keys() {
    for branch in ["if(c){i=0;}", "while(c){i=0;}"] {
        let source =
            format!("template T(){{signal input c;signal a[2];var i=1;{branch}a[i]<--1;}}");
        let lifted = fixture(&source);
        let cfg = build_cfg(&lifted.hir, lifted.hir.definition("T").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let path = witnesses(&cfg)[0].clone();
        for budget in 0..160 {
            let facts = analyze(&lifted.hir, &cfg, &field, Some(budget)).unwrap();
            assert!(facts.exact_access_key(&path).certified().is_none(), "{branch}, {budget}");
        }
    }
}

#[test]
fn exact_keys_keep_internal_elements_and_component_instances_distinct() {
    let lifted = fixture(concat!(
        "template C(){signal input x;signal output y;y<--x;}",
        "template T(){component c[2];c[0]=C();c[1]=C();c[0].x<--1;c[1].x<--1;}",
    ));
    let cfg = build_cfg(&lifted.hir, lifted.hir.definition("T").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&lifted.hir, &cfg, &field, None).unwrap();
    let paths = witnesses(&cfg);
    let left = facts.exact_access_key(&paths[0]);
    let right = facts.exact_access_key(&paths[1]);
    assert!(!left.certified().unwrap().may_alias(right.certified().unwrap()));
}
