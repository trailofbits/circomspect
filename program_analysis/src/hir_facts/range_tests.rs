use std::collections::BTreeMap;
use std::fs;

use abstract_interpretation::graph::FlowGraph;
use parser::hir::{lift_project, DefinitionRef, ExprKind, HirProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::{build_cfg, CfgNodeKind};
use crate::hir_facts::{analyze, analyze_with_scalar_parameters, FieldContext, Range};

fn fixture(source: &str) -> HirProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-range-isolation-{}-{:?}",
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
    lifted.hir
}

#[test]
fn repeated_ranges_keep_their_field_parameter_and_budget_scope() {
    let hir = fixture("function F(n){return n+2**254;}");
    let definition = hir.definition("F").unwrap();
    let DefinitionRef::Function(id) = definition else { panic!("function") };
    let parameter = hir.function(id).unwrap().parameters[0];
    let cfg = build_cfg(&hir, definition).unwrap();
    let expression = cfg
        .nodes()
        .iter()
        .find_map(|site| {
            let CfgNodeKind::Return(value) = cfg.node(*site)?.kind else { return None };
            Some(value)
        })
        .unwrap();
    for curve in [Curve::Bn254, Curve::Goldilocks, Curve::Bls12_381] {
        let field = FieldContext::for_curve(curve);
        for value in [1, 2, 0] {
            let seeds = BTreeMap::from([(parameter, field.canonical(value.into()))]);
            let complete =
                analyze_with_scalar_parameters(&hir, &cfg, &field, seeds.clone(), None).unwrap();
            let incomplete =
                analyze_with_scalar_parameters(&hir, &cfg, &field, seeds, Some(0)).unwrap();
            let expected = field.canonical((num_bigint::BigInt::from(1) << 254) + value);
            for _ in 0..3 {
                assert_eq!(
                    complete.range(expression).certified(),
                    Some(&Range::Exact(expected.clone()))
                );
                assert!(incomplete.range(expression).unavailable().is_some());
            }
        }
        let symbolic = analyze(&hir, &cfg, &field, None).unwrap();
        assert!(symbolic.range(expression).unavailable().is_some());
    }
}

#[test]
fn repeated_range_queries_never_substitute_one_unrolled_index_value() {
    let hir = fixture("template T(){signal output out[3];for(var i=0;i<3;i++){out[i]<==i;}}");
    let cfg = build_cfg(&hir, hir.definition("T").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let index = hir
        .expressions()
        .iter()
        .filter_map(|expression| {
            let ExprKind::Access(path) = &expression.kind else { return None };
            (hir.symbol(path.root)?.name == "i").then_some(expression.id)
        })
        .next_back()
        .unwrap();
    for _ in 0..3 {
        assert_eq!(facts.range(index).certified(), Some(&Range::Canonical));
    }
}
