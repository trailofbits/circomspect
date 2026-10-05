use std::fs;

use abstract_interpretation::graph::FlowGraph;
use circomspect_program_analysis::hir_cfg::{build_cfg, CfgNodeKind};
use circomspect_program_analysis::hir_facts::{analyze, FieldContext, Range};
use num_bigint_dig::BigInt;
use parser::hir::lift_project;
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn returned_range(expression: &str, curve: Curve) -> Option<Range> {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-shifts-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, format!("function Check(n){{return {expression};}}")).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty());
    assert!(lifted.diagnostics.is_empty());
    let hir = lifted.hir;
    let cfg = build_cfg(&hir, hir.definition("Check").unwrap()).unwrap();
    let field = FieldContext::for_curve(curve);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let returned = cfg
        .nodes()
        .iter()
        .find_map(|site| {
            let CfgNodeKind::Return(value) = cfg.node(*site)?.kind else { return None };
            Some(value)
        })
        .unwrap();
    facts.range(returned).certified().cloned()
}

#[test]
fn shifts_follow_masked_field_semantics_and_reverse_for_negative_counts() {
    for (curve, width) in [(Curve::Bn254, 254), (Curve::Bls12_381, 255), (Curve::Goldilocks, 64)] {
        let field = FieldContext::for_curve(curve.clone());
        for (expression, expected) in [
            ("1 << 8".to_owned(), BigInt::from(256)),
            ("256 >> 8".to_owned(), BigInt::from(1)),
            ("17 << 0".to_owned(), BigInt::from(17)),
            ("17 >> 0".to_owned(), BigInt::from(17)),
            ("1 << (-1)".to_owned(), BigInt::from(0)),
            ("1 >> (-1)".to_owned(), BigInt::from(2)),
            (format!("1 << {width}"), BigInt::from(0)),
            (format!("1 << {}", width - 1), BigInt::from(1) << (width - 1)),
            (format!("1 >> {width}"), BigInt::from(0)),
            ("1 << 512".to_owned(), BigInt::from(0)),
            ("1 >> (-512)".to_owned(), BigInt::from(0)),
        ] {
            assert_eq!(
                returned_range(&expression, curve.clone()),
                Some(Range::Exact(field.canonical(expected))),
                "{curve:?}: {expression}"
            );
        }
    }
}

#[test]
fn shifts_beyond_the_evaluation_budget_or_with_unknown_counts_stay_unknown() {
    for expression in ["1 << 513", "1 >> 513", "1 << (-513)", "1 >> (-513)"] {
        assert_eq!(
            returned_range(expression, Curve::Bn254),
            Some(Range::Canonical),
            "{expression}"
        );
    }
    assert_eq!(returned_range("1 << n", Curve::Bn254), None);
}
