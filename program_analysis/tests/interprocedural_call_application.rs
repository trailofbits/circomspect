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

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::{FieldContext, Incidence, Range};
use circomspect_program_analysis::interprocedural::{
    ArgumentValue, FunctionEffect, FunctionSummary, PortSummary, ProjectSummaries, SummaryFact,
    WitnessSite,
};
use circomspect_program_analysis::new_rules::RuleContext;
use parser::hir::{lift_project, DefinitionRef, LiftedProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-call-application-{}-{:?}",
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

fn function_summary(source: &str, name: &str) -> SummaryFact<FunctionSummary> {
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition(name).unwrap();
    let DefinitionRef::Function(function) = definition else { panic!("function") };
    let context = provider.symbolic_context_for(definition).unwrap();
    provider.function(function, &context)
}

struct OutputFacts {
    port: SummaryFact<PortSummary>,
    read: SummaryFact<bool>,
    witnesses: SummaryFact<Vec<WitnessSite>>,
}

fn output_facts(source: &str, arguments: Option<&[i64]>, indices: &[usize]) -> OutputFacts {
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let DefinitionRef::Template(template) = definition else { panic!("template T") };
    let context = match arguments {
        Some(arguments) => {
            let field = FieldContext::for_curve(Curve::Bn254);
            let mut values = Vec::new();
            for argument in arguments {
                values.push(ArgumentValue::Scalar(field.canonical((*argument).into())));
            }
            provider.context_for(definition, values).unwrap()
        }
        None => provider.symbolic_context_for(definition).unwrap(),
    };
    let port = lifted.hir.template(template).unwrap().ports[0];
    OutputFacts {
        port: provider.template_port_at(template, &context, port, indices),
        read: provider.template_port_read(template, &context, port),
        witnesses: provider.template_port_witnesses(template, &context, port),
    }
}

fn assert_fixed_output(facts: &OutputFacts, expected: i64) {
    let port = facts.port.certified().unwrap();
    assert_eq!(port.incidence(), Incidence::Must);
    let field = FieldContext::for_curve(Curve::Bn254);
    assert_eq!(port.fixed_value(), Some(&field.canonical(expected.into())));
}

#[test]
fn sequential_and_nested_calls_agree_with_direct_inlining() {
    let prefix = "function F(){return 7;} function H(x){return x+2;}";
    for (body, inline) in [
        ("var a=F();var b=H(a);return b;", "var a=7;var b=a+2;return b;"),
        ("return H(F());", "return 9;"),
        ("var a=F();return H(a)+1;", "var a=7;return (a+2)+1;"),
    ] {
        let source = format!("{prefix} function G(){{{body}}} function Inline(){{{inline}}}");
        let actual = function_summary(&source, "G");
        let expected = function_summary(&source, "Inline");
        let actual = actual.certified().and_then(FunctionSummary::complete_return);
        let expected = expected.certified().and_then(FunctionSummary::complete_return);
        assert!(expected.is_some(), "inlined body: {inline}");
        assert_eq!(actual, expected, "called body: {body}");
    }
}

#[test]
fn template_call_rhs_uses_the_exact_parameter_context() {
    let source =
        concat!("function F(n){return n+1;}", "template T(n){signal output out;out<==F(n);}");
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let DefinitionRef::Template(template) = definition else { panic!("template T") };
    let output = lifted.hir.template(template).unwrap().ports[0];
    let field = FieldContext::for_curve(Curve::Bn254);
    for value in [0, 1, 7, 1, 0] {
        let context = provider
            .context_for(definition, vec![ArgumentValue::Scalar(field.canonical(value.into()))])
            .unwrap();
        let facts = OutputFacts {
            port: provider.template_port(template, &context, output),
            read: provider.template_port_read(template, &context, output),
            witnesses: provider.template_port_witnesses(template, &context, output),
        };
        assert_fixed_output(&facts, value + 1);
        assert_eq!(facts.witnesses.certified().unwrap().len(), 1);
    }
    let context = provider.symbolic_context_for(definition).unwrap();
    let symbolic = provider.template_port(template, &context, output);
    assert!(symbolic.certified().and_then(PortSummary::fixed_value).is_none());
}

#[test]
fn call_results_prune_the_same_template_branch_as_inlined_values() {
    for value in [0, 1] {
        let source = format!(
            "function F(){{return {value};}} \
             template T(){{signal output out;if(F()){{out<==2;}}else{{out<==7;}}}}"
        );
        let called = output_facts(&source, None, &[]);
        let inline =
            format!("template T(){{signal output out;if({value}){{out<==2;}}else{{out<==7;}}}}");
        let inline = output_facts(&inline, None, &[]);
        assert_fixed_output(&called, if value == 0 { 7 } else { 2 });
        assert_eq!(
            called.port.certified().unwrap().fixed_value(),
            inline.port.certified().unwrap().fixed_value()
        );
    }
}

#[test]
fn a_scalar_call_result_cannot_validate_an_aggregate_assignment() {
    for assignment in ["out<==F();", "out<--F();"] {
        let source =
            format!("function F(){{return 7;}} template T(){{signal output out[2];{assignment}}}");
        for index in [0, 1] {
            let facts = output_facts(&source, None, &[index]);
            assert!(facts.port.certified().is_none(), "{assignment}: {:?}", facts.port);
            assert!(facts.witnesses.certified().is_none());
        }
    }
}

#[test]
fn required_parameter_index_writes_respect_concrete_argument_shapes() {
    for (argument, index) in [("1", 0), ("[2]", 1)] {
        let source = format!(
            "function F(n){{n[{index}]=1;return 7;}} \
             template T(){{var unused=F({argument});signal output out;out<==1;}}"
        );
        let facts = output_facts(&source, None, &[]);
        assert!(facts.port.certified().is_none(), "{source}: {:?}", facts.port);
        assert!(facts.read.certified().is_none(), "{source}: {:?}", facts.read);
        assert!(facts.witnesses.certified().is_none(), "{source}: {:?}", facts.witnesses);
    }
    let valid = concat!(
        "function F(n){n[0]=1;return 7;}",
        "template T(){var unused=F([2]);signal output out;out<==1;}"
    );
    assert_fixed_output(&output_facts(valid, None, &[]), 1);
}

#[test]
fn definitely_failing_calls_invalidate_later_template_certificates() {
    let prefix = concat!(
        "function Fail(){assert(0);return 7;}",
        "function Wrapper(){var x=Fail();return 9;}",
        "function Ignore(x){return 1;}"
    );
    for call in ["Fail()", "Wrapper()", "Ignore(Fail())"] {
        let source =
            format!("{prefix} template T(){{var unused={call};signal output out;out<==1;}}");
        let facts = output_facts(&source, None, &[]);
        assert!(facts.port.certified().is_none(), "{call}: {:?}", facts.port);
        assert!(facts.read.certified().is_none(), "{call}: {:?}", facts.read);
        assert!(facts.witnesses.certified().is_none(), "{call}: {:?}", facts.witnesses);
    }
}

#[test]
fn opaque_and_unexecuted_calls_preserve_independent_template_facts() {
    let prefix = "function Fail(){assert(0);return 7;} function Valid(){return 7;}";
    for statement in ["var x=Missing();", "if(0){var x=Fail();}", "var x=Valid();"] {
        let source = format!("{prefix} template T(){{{statement}signal output out;out<==1;}}");
        assert_fixed_output(&output_facts(&source, None, &[]), 1);
    }
}

#[test]
fn conditional_returns_do_not_supply_complete_call_values() {
    let prefix = "function F(n){assert(n);return 7;}";
    let source = format!("{prefix} template T(n){{signal output out;out<==F(n);}}");
    assert_fixed_output(&output_facts(&source, Some(&[1]), &[]), 7);
    assert!(output_facts(&source, Some(&[0]), &[]).port.certified().is_none());
    assert!(output_facts(&source, None, &[]).port.certified().is_none());
    let independent =
        format!("{prefix} template T(n){{var unused=F(n);signal output out;out<==1;}}");
    assert_fixed_output(&output_facts(&independent, None, &[]), 1);
}

#[test]
fn specializing_a_return_value_preserves_callee_logging_effects() {
    let source =
        concat!("function Log(x){log(x);return 7;}", "function G(){var unused=Log(9);return 1;}");
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("G").unwrap();
    let DefinitionRef::Function(function) = definition else { panic!("function G") };
    let context = provider.symbolic_context_for(definition).unwrap();
    let effects = provider.function_effects(function, &context);
    assert!(effects.certified().unwrap().contains(FunctionEffect::Log));
    let summary = provider.function(function, &context);
    let field = FieldContext::for_curve(Curve::Bn254);
    assert_eq!(
        summary.certified().and_then(FunctionSummary::complete_return),
        Some(&Range::Exact(field.canonical(1.into())))
    );
}

#[test]
fn resolved_calls_do_not_leave_a_spurious_incomplete_definition() {
    for value in ["7", "F()"] {
        let source = format!(
            "function F(){{return 7;}} template T(){{var x={value};signal output out;out<==x;}}"
        );
        let lifted = fixture(&source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("T").unwrap();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let evidence = provider.symbolic_root(definition).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
        assert!(context.validated_definition().is_ok(), "assignment: x={value}");
    }
}

#[test]
fn required_parameter_writes_respect_the_original_argument_rank() {
    for (body, argument) in [("n=[1];return 7;", "2"), ("n=1;return 7;", "[2]")] {
        let source = format!(
            "function F(n){{{body}}} template T(){{var unused=F({argument});\
             signal output out;out<==1;}}"
        );
        let facts = output_facts(&source, None, &[]);
        assert!(facts.port.certified().is_none(), "{source}: {:?}", facts.port);
        assert!(facts.read.certified().is_none(), "{source}: {:?}", facts.read);
        assert!(facts.witnesses.certified().is_none(), "{source}: {:?}", facts.witnesses);
    }
    for assignment in ["n=[1];", "n=[1,2];"] {
        let source = format!(
            "function F(n){{{assignment}return 7;}} template T(){{var unused=F([2]);\
             signal output out;out<==1;}}"
        );
        assert_fixed_output(&output_facts(&source, None, &[]), 1);
    }
}

#[test]
fn writes_do_not_enlarge_original_parameter_bounds() {
    let source = concat!(
        "function F(n){n=[1,2];var ignored=n[1];return 7;}",
        "template T(){var unused=F([2]);signal output out;out<==1;}"
    );
    let facts = output_facts(source, None, &[]);
    assert!(facts.port.certified().is_none(), "invalid program certified port: {:?}", facts.port);
    assert!(facts.read.certified().is_none());
    assert!(facts.witnesses.certified().is_none());
}

#[test]
fn scalar_subarray_target_cannot_receive_array() {
    for (body, argument) in [("var x[1];x[0]=n;", "[2]"), ("var x=n[0];", "[[2]]")] {
        let source = format!(
            "function F(n){{{body}return 7;}} \
             template T(){{var unused=F({argument});signal output out;out<==1;}}"
        );
        let facts = output_facts(&source, None, &[]);
        assert!(
            facts.port.certified().is_none(),
            "invalid program certified port: {source}: {:?}",
            facts.port
        );
        assert!(facts.read.certified().is_none());
        assert!(facts.witnesses.certified().is_none());
    }
}
