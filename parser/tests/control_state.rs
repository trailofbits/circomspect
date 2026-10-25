// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(clippy::allow_attributes, clippy::expect_used, clippy::unwrap_used)]

use std::fmt::Write;
use std::fs;

use circomspect_parser::hir::{lift_project, Knownness, LiftedProject, ValueEvidence};
use circomspect_parser::new_frontend::{load_sources, Version, VersionPolicy};

fn lift(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-control-state-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let project = load_sources(&[path], &[], VersionPolicy::new(Version::new(2, 2, 3)));
    let result = lift_project(&project);
    fs::remove_dir_all(directory).unwrap();
    assert!(result.syntax_diagnostics.is_empty(), "{:?}", result.syntax_diagnostics);
    result
}

fn states(result: &LiftedProject, name: &str) -> Vec<(Knownness, ValueEvidence)> {
    let mut states = Vec::new();
    for symbol in result.hir.symbols() {
        if symbol.name == name {
            states.push((symbol.knownness, symbol.value_evidence));
        }
    }
    states
}

#[test]
fn branch_join_preserves_symmetry_absent_else_and_deferred_evidence() {
    for branches in ["if(n){x=n;}else{x=1;}", "if(n){x=1;}else{x=n;}", "if(n){x=n;}"] {
        let source = format!("function F(n){{var x=0;{branches}return x;}}");
        let result = lift(&source);
        assert_eq!(
            states(&result, "x"),
            [(Knownness::ParameterDependent, ValueEvidence::Deferred)]
        );
    }
    let result = lift("template T(){signal input w;var x=w;if(1){x=1;}assert(x);}");
    assert_eq!(states(&result, "x"), [(Knownness::WitnessDependent, ValueEvidence::Checked)]);
}

#[test]
fn loop_join_includes_body_and_step_before_a_later_overwrite() {
    for statement in ["for(var i=0;i<1;x=1){x=w;}", "for(var i=0;i<1;x=w){x=1;}", "while(1){x=w;}"]
    {
        let source = format!("template T(){{signal input w;var x=0;{statement}assert(x);}}");
        let result = lift(&source);
        assert_eq!(states(&result, "x"), [(Knownness::WitnessDependent, ValueEvidence::Checked)]);
    }
}

#[test]
fn branch_local_suffixes_keep_distinct_shadowed_state() {
    let result = lift(concat!(
        "function F(n){var x=1;if(n){var x=n;}else{var x=2;}",
        "for(var i=0;i<1;i++){var x=n;}while(0){var x=3;}return x;}"
    ));
    assert_eq!(
        states(&result, "x"),
        [
            (Knownness::Constant, ValueEvidence::Checked),
            (Knownness::ParameterDependent, ValueEvidence::Deferred),
            (Knownness::Constant, ValueEvidence::Checked),
            (Knownness::ParameterDependent, ValueEvidence::Deferred),
            (Knownness::Constant, ValueEvidence::Checked),
        ]
    );
}

#[test]
fn control_state_preserves_complete_diagnostics_and_incomplete_records() {
    let cases = [
        ("then deferred", "function F(n){var x=0;if(n){x=n;}else{x=1;}assert(x);return x;}"),
        ("else deferred", "function F(n){var x=0;if(n){x=1;}else{x=n;}assert(x);return x;}"),
        ("absent else", "template T(){signal input w;var x=w;if(1){x=1;}signal a[x];}"),
        (
            "body then overwrite",
            "template T(){signal input w;var x=0;for(var i=0;i<1;x=1){x=w;}signal a[x];}",
        ),
        (
            "step only",
            "template T(){signal input w;var x=0;for(var i=0;i<1;x=w){x=1;}signal a[x];}",
        ),
        ("while body", "template T(){signal input w;var x=0;while(1){x=w;}signal a[x];}"),
        ("shadowed branches", "function F(n){var x=1;if(n){var x=n;}else{var x=2;}return x;}"),
    ];
    let mut records = String::new();
    for (name, source) in cases {
        let result = lift(source);
        writeln!(records, "{name}: {:#?}", (&result.diagnostics, &result.incomplete)).unwrap();
    }
    assert_eq!(records, include_str!("fixtures/control_state.txt"));
}

#[test]
fn expression_properties_preserve_all_diagnostics_and_incomplete_records() {
    let result = lift(include_str!("fixtures/expression_properties.circom"));
    let records = format!("{:#?}\n", (&result.diagnostics, &result.incomplete));
    assert_eq!(records, include_str!("fixtures/expression_properties.txt"));
}
