use abstract_interpretation::lattice::Lattice;
use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::{analyze, Degree, FieldContext, Range};
use parser::hir::{lower_project, ExprKind};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;
use std::fmt::Debug;
use std::fs;

fn check_laws<T: Lattice + Debug>(values: &[T]) {
    for a in values {
        assert!(T::bottom().leq(a));
        assert!(a.leq(a));
        let mut idempotent = a.clone();
        assert!(!idempotent.join_assign(a));
        for b in values {
            let mut left = a.clone();
            let changed = left.join_assign(b);
            assert_eq!(changed, left != *a);
            assert!(a.leq(&left));
            assert!(b.leq(&left));
            let mut reverse = b.clone();
            reverse.join_assign(a);
            assert_eq!(left, reverse);
            for c in values {
                let mut first = left.clone();
                first.join_assign(c);
                let mut second = b.clone();
                second.join_assign(c);
                let mut other = a.clone();
                other.join_assign(&second);
                assert_eq!(first, other);
                if a.leq(b) && b.leq(c) {
                    assert!(a.leq(c));
                }
            }
        }
    }
}

#[test]
fn actual_range_and_degree_domains_obey_lattice_laws() {
    let field = FieldContext::for_curve(Curve::Bn254);
    check_laws(&[
        Range::Unreachable,
        Range::Exact(field.canonical(0.into())),
        Range::Exact(field.canonical(1.into())),
        Range::Canonical,
    ]);
    let degrees = [
        Degree::Unreachable,
        Degree::Constant,
        Degree::Linear,
        Degree::Quadratic,
        Degree::Unbounded,
    ];
    check_laws(&degrees);
    for left in degrees {
        for right in degrees {
            for factor in degrees {
                if left.leq(&right) {
                    assert!(left.multiply(factor).leq(&right.multiply(factor)));
                }
            }
        }
    }
}

#[test]
fn real_hir_range_degree_and_dependencies_are_distinct() {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-phase4-domains-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("domains.circom");
    fs::write(&path, "template Check(){signal input x; signal output y; y <== x*x;}").unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lowered = lower_project(&loaded);
    assert!(lowered.diagnostics.is_empty());
    let hir = &lowered.hir;
    let cfg = build_cfg(hir, hir.definition("Check").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(hir, &cfg, &field, None).unwrap();
    let product = hir
        .expressions()
        .iter()
        .find_map(|expression| match expression.kind {
            ExprKind::Binary {
                operator: parser::new_frontend::BinaryOperator::Multiply, ..
            } => Some(expression.id),
            _ => None,
        })
        .unwrap();
    assert_eq!(facts.degree(product).certified(), Some(&Degree::Quadratic));
    assert_eq!(facts.range(product).certified(), Some(&Range::Canonical));
    let dependencies = facts.dependencies(product);
    let dependencies = dependencies.certified().unwrap();
    assert_eq!(dependencies.len(), 1);
    let symbol = hir.symbol(dependencies.iter().next().unwrap().root).unwrap();
    assert_eq!(symbol.name, "x");
}
