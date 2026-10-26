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
mod support;

use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::interprocedural::{CallOwner, CallReachability, ProjectSummaries};
use circomspect_program_analysis::new_rules::{
    run_registered, RuleContext, RuleKind, RuleResult, SourceMap,
};
use parser::hir::lift_project;
use parser::frontend::{load_sources, LoadedProject, Version, VersionPolicy};
use program_structure::report::MessageCategory;
use program_structure::utils::constants::Curve;
use serde_json::Value;

fn load_fixture(source: &str) -> LoadedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-constraints-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)))
}

fn inspect(source: &str, budget: Option<usize>) -> (LoadedProject, RuleResult) {
    let loaded = load_fixture(source);
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let evidence = if lifted.hir.mains().is_empty() {
        let definition = lifted.hir.definition("T").unwrap();
        provider.symbolic_root(definition).unwrap()
    } else {
        let site = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph().reachable_main_call(site.id(), &lifted.hir)
        else {
            panic!("main is reachable")
        };
        provider.main_evidence(&call).unwrap()
    };
    let definition = evidence.context().definition();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, budget).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    (loaded, run_registered(&context).unwrap())
}

fn count(result: &RuleResult, kind: RuleKind) -> usize {
    result.findings().iter().filter(|finding| finding.kind() == kind).count()
}

fn assert_abstention(result: &RuleResult, kind: RuleKind) {
    assert_eq!(count(result, kind), 0);
    assert!(result.abstentions().iter().any(|item| item.kind == kind));
}

fn assert_rendered(loaded: &LoadedProject, result: &RuleResult, kind: RuleKind) {
    let findings: Vec<_> =
        result.findings().iter().filter(|finding| finding.kind() == kind).cloned().collect();
    assert_eq!(findings.len(), 1);
    let source = &loaded.files[0];
    let sources = SourceMap::from_loaded(loaded, &[source.id]).unwrap();
    let report = findings[0].to_report(&sources).unwrap();
    assert_eq!(report.id(), kind.code().id());
    assert_eq!(report.category(), &MessageCategory::Warning);
    assert_eq!(report.primary().len(), 1);
    let span = &report.primary()[0].range;
    assert!(span.end > span.start);
    let output = source.path.with_extension("sarif.json");
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Info, &[], &output).unwrap(),
        (1, 1)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
    let item = &sarif["runs"][0]["results"][0];
    assert_eq!(item["ruleId"], kind.code().id());
    assert_eq!(item["level"], "warning");
    if kind == RuleKind::RedundantWitnessAssignment {
        let message = concat!(
            "The normalized equation of this witness assignment is already generated ",
            "on every reachable path."
        );
        assert_eq!(report.message(), message);
        assert_eq!(item["message"]["text"], message);
    }
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Error, &[], &output).unwrap(),
        (0, 0)
    );
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Info, &[&kind.code().id()], &output)
            .unwrap(),
        (0, 0)
    );
}

#[test]
fn witness_only_outputs_emit_without_treating_constants_as_constraints() {
    for value in
        ["0", "1", "21888242871839275222246405745257275088548364400416034343698204186575808495616"]
    {
        let source = format!("template T(){{signal output out;out<--{value};}}");
        let (loaded, result) = inspect(&source, None);
        assert_eq!(count(&result, RuleKind::SignalAssignment), 1, "{source}");
        assert_rendered(&loaded, &result, RuleKind::SignalAssignment);
    }
    let (loaded, reversed) = inspect("template T(){signal output out;1-->out;}", None);
    assert_eq!(count(&reversed, RuleKind::SignalAssignment), 1);
    assert_rendered(&loaded, &reversed, RuleKind::SignalAssignment);
}

#[test]
fn generated_constraints_and_transitive_dependencies_suppress_operator_findings() {
    for body in ["out<==1;", "out<--1;out===1;", "out<--1;var x=out;x===1;"] {
        let (_, result) = inspect(&format!("template T(){{signal output out;{body}}}"), None);
        assert_eq!(count(&result, RuleKind::SignalAssignment), 0, "{body}");
    }
}

#[test]
fn exact_array_elements_are_distinct_and_symbolic_aliases_abstain() {
    let source = "template T(){signal output out[2];out[0]<--1;out[1]<==1;}";
    let (loaded, result) = inspect(source, None);
    assert_eq!(count(&result, RuleKind::SignalAssignment), 1);
    assert_rendered(&loaded, &result, RuleKind::SignalAssignment);
    for body in ["out[i]<--1;", "out[0]<--1;out[i]===1;"] {
        let source = format!("template T(){{signal input i;signal output out[2];{body}}}");
        let (_, result) = inspect(&source, None);
        assert_abstention(&result, RuleKind::SignalAssignment);
    }
}

#[test]
fn dead_writes_do_not_warn_and_unresolved_values_or_budgets_abstain() {
    let (_, dead) = inspect("template T(){signal output out;if(0){out<--1;}}", None);
    assert_eq!(count(&dead, RuleKind::SignalAssignment), 0);
    for body in ["out<--Missing();", "if(n){out<--1;}"] {
        let source = format!("template T(n){{signal output out;{body}}}");
        let (_, result) = inspect(&source, None);
        assert_eq!(count(&result, RuleKind::SignalAssignment), 0);
        assert!(
            result.abstentions().iter().any(|a| a.kind == RuleKind::SignalAssignment),
            "{body}"
        );
    }
    let (_, pending) = inspect("template T(){signal output out;out<--1;}", Some(0));
    assert_abstention(&pending, RuleKind::SignalAssignment);
}

#[test]
fn failed_template_execution_cannot_supply_zero_incidence_findings() {
    for failure in ["assert(0);", "var x=1/0;"] {
        let source = format!("template T(){{{failure}signal output out;out<--1;}}");
        let (_, result) = inspect(&source, None);
        assert_abstention(&result, RuleKind::SignalAssignment);
    }
}

#[test]
fn complete_nested_function_calls_preserve_the_witness_only_operator() {
    let source = concat!(
        "function F(){return 1;} function G(){return F();}",
        "template T(){signal output out;out<--G();}",
    );
    let (loaded, result) = inspect(source, None);
    assert_eq!(count(&result, RuleKind::SignalAssignment), 1);
    assert_rendered(&loaded, &result, RuleKind::SignalAssignment);
}

#[test]
fn equivalent_exact_paths_are_deduplicated_across_witness_branches() {
    let source = concat!(
        "template T(){signal input c;signal output out[1];",
        "if(c){out[0]<--1;}else{out[0x0]<--2;}}",
    );
    let (loaded, result) = inspect(source, None);
    assert_eq!(count(&result, RuleKind::SignalAssignment), 1);
    assert_rendered(&loaded, &result, RuleKind::SignalAssignment);
}

#[test]
fn called_outputs_and_internal_signals_abstain_without_incoming_constraint_closure() {
    for extra in ["", "c.out===1;"] {
        let source = format!(
            "template C(){{signal output out;out<--1;signal s;s<--1;}} \
             template T(){{component c=C();{extra}}} component main=T();"
        );
        let loaded = load_fixture(&source);
        let lifted = lift_project(&loaded);
        assert!(lifted.diagnostics.is_empty());
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let main = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(main) =
            provider.graph().reachable_main_call(main.id(), &lifted.hir)
        else {
            panic!("main")
        };
        let evidence = provider.main_evidence(&main).unwrap();
        let definition = evidence.context().definition();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let call = provider.graph().calls_from(CallOwner::Definition(definition))[0];
        let CallReachability::Reachable(call) = provider.graph().reachable_call(call.id(), &facts)
        else {
            panic!("child")
        };
        let evidence = provider.call_evidence(&call, &facts, &evidence).unwrap();
        let cfg = build_cfg(&lifted.hir, evidence.context().definition()).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
        let result = run_registered(&context).unwrap();
        assert_abstention(&result, RuleKind::SignalAssignment);
        assert_abstention(&result, RuleKind::UnconstrainedSignal);
    }
}

#[test]
fn independent_output_indices_follow_values_at_their_own_sites() {
    for (body, expected) in [
        ("var i=0;out[i]<--1;i=1;out[i]<--1;out[i]===1;", 1),
        ("out[0]<--1;var i=0;out[i]===1;", 0),
        ("out[0x0]<--1;out[0]===1;", 0),
        ("out[2]<--1;", 0),
    ] {
        let source = format!("template T(){{signal output out[2];{body}}}");
        let (_, result) = inspect(&source, None);
        assert_eq!(count(&result, RuleKind::SignalAssignment), expected, "{source}");
    }
}

#[test]
fn internal_signal_zero_incidence_includes_constants_and_unused_declarations() {
    for statement in ["", "s<--0;", "s<--1;"] {
        let source = format!("template T(){{signal s;{statement}}}");
        let (loaded, result) = inspect(&source, None);
        assert_eq!(count(&result, RuleKind::UnconstrainedSignal), 1, "{source}");
        assert_rendered(&loaded, &result, RuleKind::UnconstrainedSignal);
    }
}

#[test]
fn internal_signal_constraints_and_exported_ports_are_near_misses() {
    for source in [
        "template T(){signal s;s<==1;}",
        "template T(){signal s;s<--1;s===1;}",
        "template T(){signal s;s<--1;var x=s;x===1;}",
        "template T(){signal input s;}",
        "template T(){signal output s;s<--1;}",
    ] {
        let (_, result) = inspect(source, None);
        assert_eq!(count(&result, RuleKind::UnconstrainedSignal), 0, "{source}");
    }
}

#[test]
fn internal_array_paths_keep_distinct_constraints_and_deduplicate_reads() {
    let source = "template T(){signal s[2];s[0]<--1;s[1]<==1;var x=s[0];var y=s[0x0];}";
    let (loaded, result) = inspect(source, None);
    assert_eq!(count(&result, RuleKind::UnconstrainedSignal), 1);
    assert_rendered(&loaded, &result, RuleKind::UnconstrainedSignal);
    let (_, symbolic) =
        inspect("template T(){signal input i;signal s[2];s[0]<--1;s[i]===1;}", None);
    assert_abstention(&symbolic, RuleKind::UnconstrainedSignal);
}

#[test]
fn internal_signal_failures_and_incomplete_bodies_cannot_support_warnings() {
    for prefix in ["assert(0);", "var x=1/0;", "var x=Missing();"] {
        let source = format!("template T(){{{prefix}signal s;s<--1;}}");
        let (_, result) = inspect(&source, None);
        assert_abstention(&result, RuleKind::UnconstrainedSignal);
    }
    let (_, pending) = inspect("template T(){signal s;s<--1;}", Some(0));
    assert_abstention(&pending, RuleKind::UnconstrainedSignal);
}

#[test]
fn internal_incidence_rejects_invalid_nested_functions_and_custom_witnesses() {
    for source in [
        concat!("function F(){assert(0);return 7;}", "template T(){var x=F();signal s;s<--1;}"),
        "pragma custom_templates;template custom T(){signal s;s<--1;}",
        "template extern_c T(){signal s;s<--1;}",
    ] {
        let (_, result) = inspect(source, None);
        assert_abstention(&result, RuleKind::UnconstrainedSignal);
    }
}

#[test]
fn internal_signal_main_context_preserves_exact_dimensions_and_bounds() {
    let source = "template T(n){signal s[n];s[0]<--1;}component main=T(1);";
    let (loaded, result) = inspect(source, None);
    assert_eq!(count(&result, RuleKind::UnconstrainedSignal), 1);
    assert_rendered(&loaded, &result, RuleKind::UnconstrainedSignal);
    for source in [
        "template T(){signal s[0];}",
        "template T(){signal s[1];s[1]<--1;}",
        "template T(n){signal s[n];s[0]<--1;}",
    ] {
        let (_, result) = inspect(source, None);
        assert_abstention(&result, RuleKind::UnconstrainedSignal);
    }
}

#[test]
fn legacy_cs0017_cases_are_adjudicated_against_exact_zero_incidence() {
    let (loaded, emit) = inspect(
        include_str!("../../tests/warnings/cases/underconstrained_signal_emit.circom"),
        None,
    );
    assert_eq!(count(&emit, RuleKind::UnconstrainedSignal), 1);
    assert_rendered(&loaded, &emit, RuleKind::UnconstrainedSignal);
    let (_, constrained) = inspect(
        include_str!("../../tests/warnings/cases/underconstrained_signal_no_finding.circom"),
        None,
    );
    assert_eq!(count(&constrained, RuleKind::UnconstrainedSignal), 0);
    let (_, incomplete) = inspect(
        include_str!("../../tests/warnings/cases/underconstrained_signal_abstain.circom"),
        None,
    );
    assert_abstention(&incomplete, RuleKind::UnconstrainedSignal);
}

#[test]
fn independent_internal_paths_keep_site_values_and_dead_constraint_edges() {
    for (body, expected) in [
        ("var i=0;s[i]<--1;i=1;s[i]===1;", 0),
        ("s[0]<--1;var i=0;s[i]===1;", 0),
        ("s[0x0]<--1;s[0]===1;", 0),
        ("s[0]<--1;if(0){s[0]===1;}", 1),
        ("s[0]<--1;if(1){s[0]===1;}", 0),
        ("s[2]<--1;", 0),
    ] {
        let source = format!("template T(){{signal s[2];{body}}}");
        let (_, result) = inspect(&source, None);
        assert_eq!(count(&result, RuleKind::UnconstrainedSignal), expected, "{source}");
    }
}

#[test]
fn independent_internal_claims_stay_scoped_to_valid_root_execution() {
    for source in [
        "function F(){assert(0);return 1;}template T(){signal s;s<--F();}",
        "template T(n){signal s;if(n){s<--1;s===1;}}",
        "template T(){signal s;s<--1;var a[0];a[0]=1;}",
    ] {
        let (_, result) = inspect(source, None);
        assert_abstention(&result, RuleKind::UnconstrainedSignal);
    }
    let (_, result) =
        inspect("template Bad(){var x=Missing();}template T(){signal s;s<--1;}", None);
    assert_eq!(count(&result, RuleKind::UnconstrainedSignal), 1);
}

#[test]
fn redundant_witness_writes_require_identical_generated_quadratic_equations() {
    for body in ["x<--a*b;x===a*b;", "x<--a*b+a*b;x===2*b*a;", "a*b-->x;x===a*b;"] {
        let source =
            format!("template T(){{signal input a;signal input b;signal output x;{body}}}");
        let (loaded, result) = inspect(&source, None);
        assert_eq!(count(&result, RuleKind::RedundantWitnessAssignment), 1, "{source}");
        assert_rendered(&loaded, &result, RuleKind::RedundantWitnessAssignment);
    }
}

#[test]
fn redundant_witness_near_misses_preserve_different_or_absent_equations() {
    for body in ["x<--a*b;", "x<--a*b;x===a+b;", "x<==a*b;", "x<--0;x===1;"] {
        let source =
            format!("template T(){{signal input a;signal input b;signal output x;{body}}}");
        let (_, result) = inspect(&source, None);
        assert_eq!(count(&result, RuleKind::RedundantWitnessAssignment), 0, "{source}");
    }
}

#[test]
fn redundant_witnesses_keep_exact_array_and_field_boundaries() {
    for source in [
        "template T(){signal input a;signal output x[2];x[0]<--a;x[0x0]===a;x[1]<==0;}",
        concat!(
            "template T(){signal input a;signal output x;",
            "x<--a+21888242871839275222246405745257275088548364400416034343698204186575808495617;",
            "x===a;}"
        ),
    ] {
        let (loaded, result) = inspect(source, None);
        assert_eq!(count(&result, RuleKind::RedundantWitnessAssignment), 1, "{source}");
        assert_rendered(&loaded, &result, RuleKind::RedundantWitnessAssignment);
    }
    let (_, different) =
        inspect("template T(){signal input a;signal output x[2];x[0]<--a;x[1]===a;}", None);
    assert_eq!(count(&different, RuleKind::RedundantWitnessAssignment), 0);
}

#[test]
fn redundant_witnesses_abstain_on_opaque_or_invalid_executions() {
    for source in [
        "template T(){signal input a;signal output x;x<--a*a*a;x===a*a*a;}",
        "template T(){signal output x;x<--Missing();x===1;}",
        "template T(){assert(0);signal output x;x<--1;x===1;}",
        "template T(){signal output x;x===1;x<--1;}",
        "template T(){signal y;signal output x;x<--y;y<--1;x===y;}",
        "template T(){signal output x[1];x[1]<--1;x[1]===1;}",
        "pragma custom_templates;template custom T(){signal output x;x<--1;x===1;}",
        "template T(){signal input i;signal output x[2];x[i]<--1;x[i]===1;}",
    ] {
        let (_, result) = inspect(source, None);
        assert_abstention(&result, RuleKind::RedundantWitnessAssignment);
    }
    let (_, budget) = inspect("template T(){signal output x;x<--1;x===1;}", Some(0));
    assert_abstention(&budget, RuleKind::RedundantWitnessAssignment);
}

#[test]
fn redundant_witnesses_preserve_nested_call_origins() {
    for constraint in ["x===1;", "x===F();"] {
        let source = format!(
            "function F(){{return 1;}}function G(){{return F();}}\
             template T(){{signal output x;x<--G();{constraint}}}"
        );
        let (loaded, result) = inspect(&source, None);
        assert_eq!(count(&result, RuleKind::RedundantWitnessAssignment), 1);
        assert_rendered(&loaded, &result, RuleKind::RedundantWitnessAssignment);
        let finding = result
            .findings()
            .iter()
            .find(|item| item.kind() == RuleKind::RedundantWitnessAssignment)
            .unwrap();
        let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
        let report = finding.to_report(&sources).unwrap();
        assert_eq!(&source[report.primary()[0].range.clone()], "x<--G()");
        assert_eq!(report.secondary().len(), 1);
        assert_eq!(&source[report.secondary()[0].range.clone()], constraint);
    }
}

#[test]
fn legacy_redundant_witness_cases_require_the_new_exact_equation_claim() {
    let (loaded, emit) =
        inspect(include_str!("../../tests/warnings/cases/redundant_witness_emit.circom"), None);
    assert_eq!(count(&emit, RuleKind::RedundantWitnessAssignment), 1);
    assert_rendered(&loaded, &emit, RuleKind::RedundantWitnessAssignment);
    let (_, different) = inspect(
        include_str!("../../tests/warnings/cases/redundant_witness_no_finding.circom"),
        None,
    );
    assert_eq!(count(&different, RuleKind::RedundantWitnessAssignment), 0);
    let (_, missing) =
        inspect(include_str!("../../tests/warnings/cases/redundant_witness_abstain.circom"), None);
    assert_abstention(&missing, RuleKind::RedundantWitnessAssignment);
}

#[test]
fn redundant_witnesses_abstain_when_generated_source_shape_is_invalid() {
    for rhs in ["a*b+a*c", "(a*b)*(c-c)", "(a-a)*b*c", "a*b*0*c", "((a-a)+1)*b*c"] {
        let source = format!(
            "template T(){{signal input a;signal input b;signal input c;\
             signal output x;x<--{rhs};x==={rhs};}}"
        );
        let (_, result) = inspect(&source, None);
        assert_abstention(&result, RuleKind::RedundantWitnessAssignment);
    }
}

#[test]
fn redundant_dead_witnesses_do_not_create_findings_or_abstention_noise() {
    for prefix in ["", "assert(0);"] {
        let source = format!("template T(){{{prefix}signal output x;if(0){{x<--1;x===1;}}}}");
        let (_, result) = inspect(&source, None);
        assert_eq!(count(&result, RuleKind::RedundantWitnessAssignment), 0);
        assert!(!result
            .abstentions()
            .iter()
            .any(|item| item.kind == RuleKind::RedundantWitnessAssignment));
    }
}

#[test]
fn independent_redundant_witnesses_distinguish_array_elements() {
    let source =
        concat!("template T(){signal output x[2];x[0]<--1;x[1]<--2;", "x[0]===1;x[1]===2;}");
    let (_, result) = inspect(source, None);
    assert_eq!(count(&result, RuleKind::RedundantWitnessAssignment), 2);
}

#[test]
fn independent_redundant_witness_origins_preserve_all_branch_constraints() {
    let source = concat!("template T(){signal output x;x<--1;", "if(1<<513){x===1;}else{x===1;}}");
    let (loaded, result) = inspect(source, None);
    assert_eq!(count(&result, RuleKind::RedundantWitnessAssignment), 1);
    let finding = result
        .findings()
        .iter()
        .find(|item| item.kind() == RuleKind::RedundantWitnessAssignment)
        .unwrap();
    let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
    let report = finding.to_report(&sources).unwrap();
    assert_eq!(report.secondary().len(), 2);
    for origin in report.secondary() {
        assert_eq!(&source[origin.range.clone()], "x===1;");
    }
}

#[test]
fn zero_incidence_rules_withhold_warnings_after_uninitialized_signal_reads() {
    for body in [
        "signal y;x<--y;y<--1;",
        "signal y;var t=y;y<--1;x<--1;",
        "signal y;log(y);y<--1;x<--1;",
        "x<--x+1;",
        "signal y;if(n){y<--1;}x<--y;",
        "signal y[2];y[0]<--1;x<--y[1];",
        "signal input y;y<--1;x<--1;",
        "signal input y[1];var t=y[1];x<--1;",
        "signal input y[2];var t=y[n];x<--1;",
    ] {
        for (declaration, kind) in [
            ("signal output x", RuleKind::SignalAssignment),
            ("signal x", RuleKind::UnconstrainedSignal),
        ] {
            let source = format!("template T(n){{{declaration};{body}}}");
            let (_, result) = inspect(&source, None);
            assert_eq!(count(&result, kind), 0, "{source}");
            assert_abstention(&result, kind);
        }
    }
}

#[test]
fn zero_incidence_rules_keep_initialized_signal_and_dead_read_controls() {
    for body in [
        "signal input y;x<--y;",
        "signal y;y<--1;x<--y;",
        "signal y[2];y[0]<--1;x<--y[0];",
        "signal y;if(1){y<--1;}x<--y;",
        "signal y;if(0){log(y);}x<--1;",
        "signal input y[2];var i=1;var t=y[i];x<--1;",
        "signal y;y<==1;x<--y;",
    ] {
        for (declaration, kind) in [
            ("signal output x", RuleKind::SignalAssignment),
            ("signal x", RuleKind::UnconstrainedSignal),
        ] {
            let source = format!("template T(){{{declaration};{body}}}");
            let (_, result) = inspect(&source, None);
            assert!(count(&result, kind) > 0, "{source}: {:?}", result.abstentions());
        }
    }
}

#[test]
fn zero_incidence_readiness_budgets_never_release_invalid_scope_warnings() {
    for budget in 0..65 {
        for (declaration, kind) in [
            ("signal output x", RuleKind::SignalAssignment),
            ("signal x", RuleKind::UnconstrainedSignal),
        ] {
            let source = format!("template T(){{{declaration};signal y;x<--y;y<--1;}}");
            let (_, result) = inspect(&source, Some(budget));
            assert_eq!(count(&result, kind), 0, "budget={budget}, {source}");
        }
    }
}

#[test]
fn invalid_child_execution_cannot_authorize_constraint_warnings() {
    let mut observed = Vec::new();
    for child in [
        "signal a;signal b;b<--a;a<--1;",
        "signal a;signal b;signal c;signal z;a<--1;b<--1;c<--1;\
         z<--a*b+a*c;z===a*b+a*c;",
    ] {
        let source = format!(
            "template Child(){{{child}}}template T(){{signal s;s<--1;\
             signal output x;x<--1;x===1;component c=Child();}}"
        );
        let (_, result) = inspect(&source, None);
        observed.push((
            count(&result, RuleKind::UnconstrainedSignal),
            count(&result, RuleKind::RedundantWitnessAssignment),
        ));
    }
    assert_eq!(observed, vec![(0, 0), (0, 0)]);
}

#[test]
fn a_later_array_index_read_requires_its_own_prior_witness_write() {
    let source = "template T(){signal output out[2];var i=0;out[i]<--1;i=1;out[i]===1;}";
    let (_, result) = inspect(source, None);
    assert_abstention(&result, RuleKind::SignalAssignment);
}

#[test]
fn invalid_generated_source_form_withholds_other_zero_incidence_warnings() {
    for (declaration, kind) in [
        ("signal output s", RuleKind::SignalAssignment),
        ("signal s", RuleKind::UnconstrainedSignal),
    ] {
        let source = format!(
            "template T(){{{declaration};s<--1;signal a;signal b;signal c;signal z;\
             a<--1;b<--1;c<--1;z<--a*b+a*c;z===a*b+a*c;}}"
        );
        let (_, result) = inspect(&source, None);
        assert_abstention(&result, kind);
    }
}
