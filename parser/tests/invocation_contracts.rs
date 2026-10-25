// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(clippy::allow_attributes, clippy::expect_used, clippy::unwrap_used)]

use std::fmt::Write;
use std::fs;

use circomspect_parser::hir::{lift_project, CallTarget, IncompleteReason, LiftedProject};
use circomspect_parser::new_frontend::{load_sources, Version, VersionPolicy};

fn lift(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-invocation-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let project = load_sources(&[path], &[], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&project);
    fs::remove_dir_all(directory).unwrap();
    lifted
}

#[test]
fn template_invocations_preserve_all_diagnostics_and_incomplete_reasons() {
    let cases = [
        ("component", "template Child(n){} template T(){signal input x; component c=Child(x,1);}"),
        (
            "parallel component",
            "template Child(n){} template T(){signal input x; component c=parallel Child(x,1);}",
        ),
        (
            "anonymous",
            "template Child(n){signal input a;} template T(){signal input x; Child(x,1)(x);}",
        ),
        ("main", "template Child(n){} component main=parallel Child(Missing(),1);"),
        (
            "nested missing",
            "template T(){component c=Missing(First()); MissingAnon(Second())();} \
             component main=MissingMain(Third());",
        ),
        (
            "wrong kind",
            "function F(n){return n;} template T(){component c=F(0); F(1)();} \
             component main=F(2);",
        ),
        (
            "grouped calls",
            "template Child(){} template T(){component c=(Child());} \
             component main=(Child());",
        ),
    ];
    let mut records = String::new();
    for (name, source) in cases {
        let result = lift(source);
        assert!(result.syntax_diagnostics.is_empty(), "{name}: {:?}", result.syntax_diagnostics);
        writeln!(records, "{name}: {:#?}", (&result.diagnostics, &result.incomplete)).unwrap();
    }
    assert_eq!(records, include_str!("fixtures/template_invocations.txt"));
}

#[test]
fn wrong_arity_wins_after_witness_parameter_validation() {
    for statement in ["component c=Child(x,1);", "Child(x,1)(x);"] {
        let source = format!(
            "template Child(n){{signal input a;}} template T(){{signal input x; {statement}}}"
        );
        let result = lift(&source);
        assert_eq!(result.diagnostics.len(), 2, "{:?}", result.diagnostics);
        assert_eq!(result.hir.components().len(), 1);
        assert_eq!(
            result.hir.components()[0].target,
            Some(CallTarget::Opaque {
                reason: IncompleteReason::Unsupported("wrong argument arity".into())
            })
        );
    }
}
