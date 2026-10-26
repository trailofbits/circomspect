// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::assert_is_empty,
    clippy::expect_used,
    clippy::format_push_string,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
mod support;

use std::collections::BTreeSet;
use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::FactBlocker;
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ProjectAnalysis, SummaryBlocker,
};
use circomspect_program_analysis::rules::{
    run_registered, AbstentionReason, RuleContext, RuleKind, RuleResult, SourceMap,
};
use parser::hir::lift_project;
use parser::frontend::{load_sources, LoadedProject, Version, VersionPolicy};
use program_structure::report::MessageCategory;
use program_structure::utils::constants::Curve;
use serde_json::Value;

fn fixture(source: &str) -> LoadedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-direct-rules-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)))
}

fn with_rules(source: &str, name: &str, test: impl FnOnce(&RuleResult, &LoadedProject)) {
    let loaded = fixture(source);
    let lifted = lift_project(&loaded);
    let definition = lifted.hir.definition(name).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    let result = run_registered(&context).unwrap();
    test(&result, &loaded);
}

fn complexity_source(branches: usize, condition: &str, linear: usize) -> String {
    let mut source = String::from("template Check(){signal input x;signal output y;var value=0;");
    for _ in 0..linear {
        source.push_str("value=value+1;");
    }
    for index in 0..branches {
        source.push_str(&format!("if({condition}){{value={index};}}"));
    }
    source.push_str("y<--value;}");
    source
}

#[test]
fn complexity_uses_reachable_edges_with_exact_threshold() {
    for (branches, expected) in [(19, None), (20, Some(21)), (21, Some(22))] {
        let source = complexity_source(branches, "x", 0);
        with_rules(&source, "Check", |result, loaded| {
            let findings: Vec<_> = result
                .findings()
                .iter()
                .filter(|finding| finding.kind() == RuleKind::Complexity)
                .collect();
            assert_eq!(findings.len(), usize::from(expected.is_some()), "branches={branches}");
            if let Some(metric) = expected {
                let sources = SourceMap::from_loaded(loaded, &[loaded.files[0].id]).unwrap();
                let report = findings[0].to_report(&sources).unwrap();
                assert!(report.message().contains(&metric.to_string()));
            }
        });
    }
}

#[test]
fn complexity_ignores_pruned_branches_and_linear_cfg_expansion() {
    for source in [complexity_source(24, "0", 0), complexity_source(19, "x", 12)] {
        with_rules(&source, "Check", |result, _| {
            assert!(result.findings().iter().all(|finding| finding.kind() != RuleKind::Complexity));
        });
    }
}

#[test]
fn dead_nested_symbolic_guard_does_not_hide_live_witness_complexity() {
    let source = complexity_source(20, "x", 0)
        .replace("template Check(){", "template Check(n){")
        .replace("var value=0;", "var value=0;if(0){if(n){value=1;}}");
    with_rules(&source, "Check", |result, loaded| {
        let finding = result
            .findings()
            .iter()
            .find(|finding| finding.kind() == RuleKind::Complexity)
            .unwrap();
        let sources = SourceMap::from_loaded(loaded, &[loaded.files[0].id]).unwrap();
        assert!(finding.to_report(&sources).unwrap().message().contains("complexity 21"));
    });
}

#[test]
fn symbolic_compile_time_branches_do_not_certify_library_complexity() {
    let source = complexity_source(20, "n", 0).replace("template Check(){", "template Check(n){");
    with_rules(&source, "Check", |result, _| {
        assert!(result.findings().iter().all(|finding| finding.kind() != RuleKind::Complexity));
        let abstention =
            result.abstentions().iter().find(|item| item.kind == RuleKind::Complexity).unwrap();
        let AbstentionReason::LocalFacts(blockers) = &abstention.reason else {
            panic!("expected deferred control blockers")
        };
        assert!(blockers.iter().any(|blocker| {
            let FactBlocker::DeferredControl(_) = blocker else { return false };
            true
        }));
    });

    let concrete = format!("{source} component main=Check(1);");
    let loaded = fixture(&concrete);
    let lifted = lift_project(&loaded);
    let definition = lifted.hir.definition("Check").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), provider.hir())
    else {
        panic!("complete main call")
    };
    let evidence = provider.main_evidence(&call).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    let result = run_registered(&context).unwrap();
    assert!(result.findings().iter().all(|finding| finding.kind() != RuleKind::Complexity));
}

#[test]
fn nested_witness_decisions_count_and_unrelated_library_errors_do_not_hide_warning() {
    let mut body = String::new();
    for index in 0..20 {
        body.push_str(&format!("if(x){{value={index};}}"));
    }
    let source = format!(
        "function Broken(){{return Missing();}} \
         template Check(){{signal input x;var value=0;if(1){{{{{body}}}}}}}"
    );
    with_rules(&source, "Check", |result, _| {
        assert_eq!(
            result
                .findings()
                .iter()
                .filter(|finding| finding.kind() == RuleKind::Complexity)
                .count(),
            1
        );
    });
}

#[test]
fn excessive_arguments_counts_validated_function_and_template_headers() {
    for (source, expected) in [
        ("function Check(a,b,c,d,e,f,g,h){return 0;}", true),
        ("template Check(a,b,c,d,e,f,g,h){signal input x;}", true),
        ("function Check(a,b,c,d,e,f,g){return 0;}", false),
        ("template Check(a,b,c,d,e,f,g){signal input x;}", false),
    ] {
        with_rules(source, "Check", |result, loaded| {
            let findings: Vec<_> = result
                .findings()
                .iter()
                .filter(|finding| finding.kind() == RuleKind::TooManyArguments)
                .collect();
            assert_eq!(findings.len(), usize::from(expected), "{source}");
            if expected {
                let sources = SourceMap::from_loaded(loaded, &[loaded.files[0].id]).unwrap();
                let report = findings[0].to_report(&sources).unwrap();
                assert!(report.message().contains('8'));
                assert!(report.message().contains('7'));
                assert_eq!(report.primary()[0].range, 9..14);
            }
        });
    }
}

#[test]
fn incomplete_body_keeps_header_finding_but_blocks_cfg_metric() {
    let source = format!(
        "template Check(a,b,c,d,e,f,g,h){{var z=Missing();{}}}",
        complexity_source(21, "a", 0).replace("template Check(){", "").replace("y<--value;}", "")
    );
    with_rules(&source, "Check", |result, _| {
        assert!(result
            .findings()
            .iter()
            .any(|finding| finding.kind() == RuleKind::TooManyArguments));
        assert!(result.findings().iter().all(|finding| finding.kind() != RuleKind::Complexity));
        assert!(result.abstentions().iter().any(|abstention| {
            abstention.kind == RuleKind::Complexity
                && abstention.reason
                    == AbstentionReason::Summary(BTreeSet::from([
                        SummaryBlocker::IncompleteDefinition,
                    ]))
        }));
    });
}

#[test]
fn unfinished_local_solver_cannot_certify_complexity() {
    let source = complexity_source(21, "x", 0);
    let loaded = fixture(&source);
    let lifted = lift_project(&loaded);
    let definition = lifted.hir.definition("Check").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, Some(0)).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    let result = run_registered(&context).unwrap();
    assert!(result.findings().iter().all(|finding| finding.kind() != RuleKind::Complexity));
    let abstention = result
        .abstentions()
        .iter()
        .find(|abstention| abstention.kind == RuleKind::Complexity)
        .unwrap();
    let AbstentionReason::LocalFacts(blockers) = &abstention.reason else {
        panic!("expected blocked local facts")
    };
    assert!(blockers.iter().any(|blocker| {
        let FactBlocker::Budget(_) = blocker else { return false };
        true
    }));
}

#[test]
fn malformed_parameter_list_cannot_emit_an_argument_warning() {
    for source in [
        "function Check(a,b,c,d,e,f,g,h,){return 0;}",
        "function Check(a,b,c,d,e,f,g,g){return 0;}",
    ] {
        let loaded = fixture(source);
        let lifted = lift_project(&loaded);
        if lifted.hir.definition("Check").is_none() {
            assert!(!lifted.syntax_diagnostics.is_empty());
            continue;
        }
        with_rules(source, "Check", |result, _| {
            assert!(result
                .findings()
                .iter()
                .all(|finding| { finding.kind() != RuleKind::TooManyArguments }));
            assert!(result
                .abstentions()
                .iter()
                .any(|item| { item.kind == RuleKind::TooManyArguments }));
        });
    }
}

#[test]
fn library_without_main_still_reports_its_own_valid_header() {
    with_rules("template Check(a,b,c,d,e,f,g,h){}", "Check", |result, loaded| {
        let finding = result
            .findings()
            .iter()
            .find(|finding| finding.kind() == RuleKind::TooManyArguments)
            .unwrap();
        let sources = SourceMap::from_loaded(loaded, &[loaded.files[0].id]).unwrap();
        let output = loaded.files[0].path.with_extension("sarif.json");
        assert_eq!(
            support::render(
                std::slice::from_ref(finding),
                &sources,
                MessageCategory::Warning,
                &[],
                &output
            )
            .unwrap(),
            (1, 1)
        );
    });
}

#[test]
fn emitted_direct_rules_keep_ids_spans_and_suppressions_in_both_renderers() {
    let source = complexity_source(20, "x", 0)
        .replace("template Check(){", "template Check(a,b,c,d,e,f,g,h){");
    with_rules(&source, "Check", |result, loaded| {
        let sources = SourceMap::from_loaded(loaded, &[loaded.files[0].id]).unwrap();
        let output = loaded.files[0].path.with_extension("sarif.json");
        let findings: Vec<_> = result
            .findings()
            .iter()
            .filter(|finding| {
                finding.kind() == RuleKind::Complexity
                    || finding.kind() == RuleKind::TooManyArguments
            })
            .cloned()
            .collect();
        assert_eq!(
            support::render(&findings, &sources, MessageCategory::Warning, &[], &output).unwrap(),
            (2, 2)
        );
        let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
        let results = sarif["runs"][0]["results"].as_array().unwrap();
        assert_eq!(results[0]["ruleId"], "CS0011");
        assert_eq!(results[1]["ruleId"], "CS0012");
        for result in results {
            assert_eq!(result["level"], "warning");
            assert_eq!(result["locations"][0]["physicalLocation"]["region"]["startLine"], 1);
            assert_eq!(result["locations"][0]["physicalLocation"]["region"]["startColumn"], 10);
            assert_eq!(result["locations"][0]["physicalLocation"]["region"]["endColumn"], 15);
        }
        assert_eq!(
            support::render(&findings, &sources, MessageCategory::Warning, &["CS0011"], &output)
                .unwrap(),
            (1, 1)
        );
        let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
        assert_eq!(sarif["runs"][0]["results"][0]["ruleId"], "CS0012");
        assert_eq!(
            support::render(&findings, &sources, MessageCategory::Warning, &["CS0012"], &output)
                .unwrap(),
            (1, 1)
        );
        let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
        assert_eq!(sarif["runs"][0]["results"][0]["ruleId"], "CS0011");
    });
}
