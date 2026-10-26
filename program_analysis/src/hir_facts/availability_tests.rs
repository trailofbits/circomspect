use std::collections::BTreeSet;
use std::fs;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use parser::hir::{lift_project, AccessPath, AccessStep, ArrayIndex, HirProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::{build_cfg, CfgNodeKind};
use crate::hir_facts::{analyze, Fact, FactBlocker, FieldContext, Range};

fn fixture(source: &str) -> HirProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-fact-availability-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let file = directory.join("case.circom");
    fs::write(&file, source).unwrap();
    let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded).hir
}

#[test]
fn certified_absence_and_empty_unavailability_are_distinct() {
    let absent = Fact::<Option<u8>>::known(None);
    assert_eq!(absent.certified(), Some(&None));
    assert_eq!(absent.unavailable(), None);
    assert_eq!(absent.as_result(), Ok(&None));
    assert_eq!(absent.into_result(), Ok(None));
    let blocked = Fact::<Option<u8>>::blocked(BTreeSet::new());
    assert_eq!(blocked.certified(), None);
    assert_eq!(blocked.unavailable(), Some(&BTreeSet::new()));
    assert_eq!(blocked.as_result(), Err(&BTreeSet::new()));
    assert_eq!(blocked.into_result(), Err(BTreeSet::new()));
    let present = Fact::known(Some(7));
    assert_eq!(present.certified(), Some(&Some(7)));
    assert_eq!(present.as_result(), Ok(&Some(7)));
    assert_eq!(present.into_result(), Ok(Some(7)));
}

#[test]
fn exact_access_and_body_write_forward_all_index_blockers() {
    let hir = fixture("template Check(){signal input i;signal output a[2];a[i]<--0;}");
    let cfg = build_cfg(&hir, hir.definition("Check").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let target = cfg
        .nodes()
        .iter()
        .find_map(|id| match &cfg.node(*id)?.kind {
            CfgNodeKind::Witness { target, .. } => Some(target),
            _ => None,
        })
        .unwrap();
    let AccessStep::Index { index: ArrayIndex::Symbolic(index), .. } = target.steps[0] else {
        panic!("symbolic index");
    };
    let blockers =
        BTreeSet::from([FactBlocker::ExternalSummary, FactBlocker::DeferredShape(index)]);
    facts.ranges.lock().unwrap().insert(index, Fact::blocked(blockers.clone()));
    assert_eq!(facts.exact_access_key(target).unavailable(), Some(&blockers));
    assert_eq!(facts.body_write_status(target).unavailable(), Some(&blockers));
    let blocked = Fact::<Range>::blocked(blockers.clone());
    assert_eq!(blocked.as_result(), Err(&blockers));
    assert_eq!(blocked.into_result(), Err(blockers));
    for range in [Range::Canonical, Range::Unreachable] {
        facts.ranges.lock().unwrap().insert(index, Fact::known(range));
        let non_exact = BTreeSet::from([FactBlocker::OpaqueExpression(index)]);
        assert_eq!(facts.exact_access_key(target).unavailable(), Some(&non_exact));
        assert_eq!(facts.body_write_status(target).unavailable(), Some(&non_exact));
    }
}

#[test]
fn witness_only_fixed_value_is_certified_absent() {
    let hir = fixture("template Check(){signal output x;x<--7;}");
    let cfg = build_cfg(&hir, hir.definition("Check").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let symbol = hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap();
    let path = AccessPath {
        root: symbol.id,
        terminal: symbol.id,
        steps: Vec::new(),
        component_input: false,
        component_output: false,
        span: symbol.span,
    };
    assert_eq!(facts.constraint_fixed(&path).certified(), Some(&None));
    assert_eq!(facts.constraint_fixed(&path).unavailable(), None);
}

#[test]
fn must_execute_preserves_foreign_query_before_budget_failure() {
    let hir = fixture("template Check(){signal output x;x<==7;}");
    let cfg = build_cfg(&hir, hir.definition("Check").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, Some(0)).unwrap();
    assert_eq!(
        facts.must_execute(NodeId::new(usize::MAX)).unavailable(),
        Some(&BTreeSet::from([FactBlocker::ForeignQuery]))
    );
    assert_eq!(
        facts.must_execute(cfg.entry()).unavailable(),
        Some(&BTreeSet::from([FactBlocker::Budget(cfg.entry())]))
    );
}
