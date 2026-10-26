// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use std::fs;

use circomspect_program_analysis::hir_facts::Incidence;
use circomspect_program_analysis::interprocedural::{ProjectAnalysis, SummaryBlocker};
use parser::hir::{lift_project, DefinitionRef, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-call-failure-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    lifted
}

fn assert_output_availability(source: &str, available: bool) {
    let lifted = fixture(source);
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let DefinitionRef::Template(template) = definition else { panic!("template T") };
    let context = provider.contexts().symbolic_context_for(definition).unwrap();
    let output = lifted.hir.template(template).unwrap().ports[0];
    let port = provider.template_port(template, &context, output);
    let read = provider.template_port_read(template, &context, output);
    let witnesses = provider.template_port_witnesses(template, &context, output);
    assert_eq!(port.certified().is_some(), available, "{source}: {port:?}");
    if !available {
        assert!(read.certified().is_none(), "{source}: {read:?}");
        assert!(witnesses.certified().is_none(), "{source}: {witnesses:?}");
    }
    if let Some(port) = port.certified() {
        assert_eq!(port.incidence(), Incidence::Must);
    }
}

#[test]
fn required_function_failures_invalidate_all_template_certificates() {
    for failure in [
        "assert(0);",
        "var x=1/0;",
        "var x=1\\0;",
        "var x=1%0;",
        "var x[-1];",
        "var x[1];x[1]=2;",
        "var x[1];var y=x[1];",
    ] {
        for call in ["Fail()", "Wrap()", "Ignore(Fail())"] {
            let source = format!(
                "function Fail(){{{failure}return 7;}} \
                 function Wrap(){{var x=Fail();return 9;}} \
                 function Ignore(x){{return 1;}} \
                 template T(){{var unused={call};signal output out;out<==1;}}"
            );
            assert_output_availability(&source, false);
        }
    }
}

#[test]
fn required_failure_uses_exact_arguments_and_callee_control_flow() {
    for (argument, available) in [(0, false), (1, true)] {
        let source = format!(
            "function Check(n){{if(n){{return 7;}}assert(0);return 9;}} \
             template T(){{var unused=Check({argument});signal output out;out<==1;}}"
        );
        assert_output_availability(&source, available);
    }
}

#[test]
fn unknown_and_unexecuted_failures_preserve_independent_facts() {
    for statement in [
        "var x=Missing();",
        "if(0){var x=Fail();}",
        "if(n){var x=Fail();}",
        "var x=Conditional(n);",
        "var x=Valid();",
    ] {
        let source = format!(
            "function Fail(){{assert(0);return 7;}} \
             function Conditional(n){{assert(n);return 7;}} \
             function Valid(){{log(7);return 7;}} \
             template T(n){{{statement}signal output out;out<==1;}}"
        );
        assert_output_availability(&source, true);
    }
}

#[test]
fn finite_recursive_calls_reach_a_proven_failing_base_case() {
    let source = concat!(
        "function F(n){if(n){return F(n-1);}assert(0);return 7;}",
        "template T(){var unused=F(2);signal output out;out<==1;}"
    );
    assert_output_availability(source, false);
}

#[test]
fn failure_scan_budget_cannot_certify_a_template() {
    let lifted = fixture(concat!(
        "function F(n){if(n){return F(n-1);}assert(0);return 7;}",
        "template T(){var unused=F(64);signal output out;out<==1;}"
    ));
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let DefinitionRef::Template(template) = definition else { panic!("template T") };
    let context = provider.contexts().symbolic_context_for(definition).unwrap();
    let output = lifted.hir.template(template).unwrap().ports[0];
    let expected = std::collections::BTreeSet::from([SummaryBlocker::ContextBudget]);
    assert_eq!(provider.template_port(template, &context, output).unavailable(), Some(&expected));
    assert_eq!(
        provider.template_port_read(template, &context, output).unavailable(),
        Some(&expected)
    );
    assert_eq!(
        provider.template_port_witnesses(template, &context, output).unavailable(),
        Some(&expected)
    );
}

#[test]
fn repeated_contexts_do_not_consume_the_failure_scan_budget() {
    assert_output_availability(
        "function F(n){if(n){return F(n-1);}return 7;} \
         template T(){var a=F(63);var b=F(63);signal output out;out<==1;}",
        true,
    );
}

#[test]
fn required_invalid_parameter_assignment_prevents_template_certificates() {
    assert_output_availability(
        "function F(n){var x=n;x=1;return 7;} \
         template T(){var unused=F([1,2]);signal output out;out<==1;}",
        false,
    );
}

#[test]
fn only_required_ternary_arms_propagate_execution_failure() {
    for (value, available) in [
        ("1?Fail():7", false),
        ("0?Fail():7", true),
        ("0?7:Fail()", false),
        ("1?7:Fail()", true),
        ("1?(0?7:Fail()):9", false),
        ("n?Fail():7", true),
    ] {
        let source = format!(
            "function Fail(){{assert(0);return 7;}} \
             template T(n){{var unused={value};signal output out;out<==1;}}"
        );
        assert_output_availability(&source, available);
    }
}
