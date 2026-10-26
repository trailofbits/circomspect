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
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ProjectSummaries, SummaryBlocker,
};
use circomspect_program_analysis::new_rules::{
    run_registered, RuleContext, RuleKind, RuleResult, SourceMap,
};
use parser::hir::lift_project;
use parser::frontend::{load_sources, LoadedProject, Version, VersionPolicy};
use program_structure::utils::constants::Curve;
use program_structure::report::MessageCategory;
use serde_json::Value;

fn fixture(source: &str) -> LoadedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-called-division-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)))
}

fn inspect(source: &str, budget: Option<usize>) -> Result<RuleResult, SummaryBlocker> {
    inspect_loaded(&fixture(source), budget)
}

fn inspect_loaded(
    loaded: &LoadedProject,
    budget: Option<usize>,
) -> Result<RuleResult, SummaryBlocker> {
    let lifted = lift_project(loaded);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Main").unwrap();
    let sites = provider.graph().calls_from(CallOwner::Main(0));
    let parent_evidence = if let Some(site) = sites.first() {
        let CallReachability::Reachable(call) =
            provider.graph().reachable_main_call(site.id(), &lifted.hir)
        else {
            panic!("reachable main")
        };
        provider.main_evidence(&call).unwrap()
    } else {
        provider.symbolic_root(parent).unwrap()
    };
    let parent_cfg = build_cfg(&lifted.hir, parent).unwrap();
    let parent_facts = provider.analyze_for_evidence(&parent_cfg, &parent_evidence, None).unwrap();
    let child = lifted.hir.definition("Quotient").unwrap();
    let site = provider
        .graph()
        .calls_from(CallOwner::Definition(parent))
        .iter()
        .find(|site| site.resolved() == Some(child))
        .copied()
        .unwrap();
    let CallReachability::Reachable(call) =
        provider.graph().reachable_call(site.id(), &parent_facts)
    else {
        panic!("reachable child")
    };
    let evidence = provider.call_evidence(&call, &parent_facts, &parent_evidence)?;
    let cfg = build_cfg(&lifted.hir, child).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, budget).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    Ok(run_registered(&context).unwrap())
}

fn source(binding: &str, parent_extra: &str, child_extra: &str) -> String {
    format!(
        "template Quotient(){{signal input divisor;signal output result;\
         result<--1/divisor;{child_extra}}}\
         template Main(){{signal input x;component child=Quotient();\
         {binding}{parent_extra}}}component main=Main();"
    )
}

fn division_count(result: &RuleResult) -> usize {
    result
        .findings()
        .iter()
        .filter(|finding| finding.kind() == RuleKind::UnconstrainedDivision)
        .count()
}

#[test]
fn witness_initialized_child_input_retains_zero_generated_incidence() {
    for binding in ["child.divisor<--x;", "child.divisor<--7;"] {
        let result = inspect(&source(binding, "", ""), None).unwrap();
        assert_eq!(division_count(&result), 1, "{:?}", result.abstentions());
    }
}

#[test]
fn generated_child_binding_or_related_constraint_prevents_zero_incidence_claim() {
    for (binding, parent, child) in [
        ("child.divisor<==x;", "", ""),
        ("child.divisor<==7;", "", ""),
        ("child.divisor<--x;", "x===7;", ""),
        ("child.divisor<--x;", "", "divisor*divisor===1;"),
    ] {
        assert_eq!(division_count(&inspect(&source(binding, parent, child), None).unwrap()), 0);
    }
}

#[test]
fn incomplete_or_invalid_caller_never_authorizes_child_zero_incidence() {
    for (binding, parent) in [
        ("", ""),
        ("child.divisor<--x;child.divisor<--7;", ""),
        ("child.divisor<--x;", "signal early;log(early);early<--1;"),
        ("child.divisor<--x;", "assert(x==1);"),
        ("child.divisor<--x;", "component other=Quotient();other.divisor<--1;"),
    ] {
        let Ok(result) = inspect(&source(binding, parent, ""), None) else { continue };
        assert_eq!(division_count(&result), 0);
        assert!(result
            .abstentions()
            .iter()
            .any(|item| item.kind == RuleKind::UnconstrainedDivision));
    }
}

#[test]
fn called_library_scope_and_incomplete_local_analysis_cannot_borrow_main_evidence() {
    let source = source("child.divisor<--x;", "", "");
    let library = source.replace("component main=Main();", "");
    assert_eq!(division_count(&inspect(&library, None).unwrap()), 0);
    for budget in [0, 1, 2, 4, 8] {
        assert_eq!(division_count(&inspect(&source, Some(budget)).unwrap()), 0, "budget {budget}");
    }
}

#[test]
fn called_division_keeps_exact_operator_span_and_both_renderer_filters() {
    let source = source("child.divisor<--x;", "", "");
    let loaded = fixture(&source);
    let result = inspect_loaded(&loaded, None).unwrap();
    let findings: Vec<_> = result
        .findings()
        .iter()
        .filter(|finding| finding.kind() == RuleKind::UnconstrainedDivision)
        .cloned()
        .collect();
    assert_eq!(findings.len(), 1);
    let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
    let report = findings[0].to_report(&sources).unwrap();
    assert_eq!(report.id(), "CS0015");
    assert_eq!(&source[report.primary()[0].range.clone()], "1/divisor");
    assert_eq!(report.to_diagnostic(true).labels[0].range, report.primary()[0].range);
    assert!(report
        .message()
        .contains("No generated constraint depends on this exact input divisor"));
    let output = loaded.files[0].path.with_extension("sarif.json");
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Warning, &[], &output).unwrap(),
        (1, 1)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
    let result = &sarif["runs"][0]["results"][0];
    assert_eq!(result["ruleId"], "CS0015");
    assert_eq!(result["level"], "warning");
    assert_eq!(
        result["locations"][0]["physicalLocation"]["region"]["startColumn"],
        report.primary()[0].range.start + 1
    );
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Warning, &["CS0015"], &output)
            .unwrap(),
        (0, 0)
    );
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Error, &[], &output).unwrap(),
        (0, 0)
    );
}

#[test]
fn internal_witness_aliases_and_unclosed_child_dependencies_abstain() {
    for source in [
        source("signal local;local<--x;child.divisor<--local;", "", ""),
        source("child.divisor<--x;", "child.divisor===7;", ""),
        source("child.divisor<--x;", "", "signal missing;log(missing);"),
        source("child.divisor<--x;", "", "assert(divisor==1);"),
        source("child.divisor<--x;", "", "component nested=Quotient();nested.divisor<--1;"),
    ] {
        let Ok(result) = inspect(&source, None) else { continue };
        assert_eq!(division_count(&result), 0);
        assert!(result
            .abstentions()
            .iter()
            .any(|item| item.kind == RuleKind::UnconstrainedDivision));
    }
}

#[test]
fn unrelated_incomplete_function_preserves_the_closed_division_scope() {
    let source = source("child.divisor<--x;", "", "").replace(
        "component main=Main();",
        "function Broken(){return Missing();}component main=Main();",
    );
    let loaded = fixture(&source);
    let lifted = lift_project(&loaded);
    assert!(!lifted.diagnostics.is_empty());
    let result = inspect_loaded(&loaded, None).unwrap();
    assert_eq!(division_count(&result), 1, "{:?}", result.abstentions());
}
