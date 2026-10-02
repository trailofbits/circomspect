mod support;

use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::interprocedural::{CallOwner, CallReachability, ProjectSummaries};
use circomspect_program_analysis::new_rules::{
    run_registered, RuleContext, RuleKind, RuleResult, SourceMap,
};
use parser::hir::lift_project;
use parser::new_frontend::{load_sources, LoadedProject, Version, VersionPolicy};
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
        ("var i=0;out[i]<--1;i=1;out[i]===1;", 1),
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
