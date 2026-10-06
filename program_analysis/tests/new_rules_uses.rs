// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
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
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ProjectSummaries, SummaryBlocker,
};
use circomspect_program_analysis::new_rules::{
    run_registered, AbstentionReason, RuleContext, RuleKind, RuleResult, SourceMap,
};
use parser::hir::lift_project;
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::report::MessageCategory;
use program_structure::utils::constants::Curve;

fn run_case(source: &str, definition: &str, test: impl FnOnce(&RuleResult, &SourceMap<'_>)) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-uses-rules-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(
        &[path],
        std::slice::from_ref(&directory),
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    let lifted = lift_project(&loaded);
    let definition = lifted.hir.definition(definition).unwrap();
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let evidence = if lifted.hir.mains().is_empty() {
        provider.symbolic_root(definition).unwrap()
    } else {
        let site = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(main) =
            provider.graph().reachable_main_call(site.id(), provider.hir())
        else {
            panic!("main must be reachable")
        };
        provider.main_evidence(&main).unwrap()
    };
    let cfg = build_cfg(provider.hir(), definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    let results = run_registered(&context).unwrap();
    let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
    test(&results, &sources);
}

fn count(results: &RuleResult, kind: RuleKind) -> usize {
    results.findings().iter().filter(|finding| finding.kind() == kind).count()
}

#[test]
fn ready_outputless_input_child_does_not_hide_an_unused_sibling_output() {
    let source = concat!(
        "template Leaf(){signal output out;out<==1;}",
        "template Empty(){signal input x;x===1;}",
        "template Parent(){component c=Leaf();component e=Empty();e.x<==1;}",
        "component main=Parent();"
    );
    run_case(source, "Parent", |results, sources| {
        let findings: Vec<_> = results
            .findings()
            .iter()
            .filter(|finding| finding.kind() == RuleKind::UnusedOutputSignal)
            .cloned()
            .collect();
        assert_eq!(findings.len(), 1);
        let path = std::env::temp_dir().join(format!(
            "circomspect-outputless-input-{}-{:?}.json",
            std::process::id(),
            std::thread::current().id()
        ));
        assert_eq!(
            support::render(&findings, sources, MessageCategory::Warning, &[], &path).unwrap(),
            (1, 1)
        );
        let sarif: serde_json::Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        let item = &sarif["runs"][0]["results"][0];
        assert_eq!(item["ruleId"], "CS0018");
        assert_eq!(item["level"], "warning");
        assert!(item["message"]["text"].as_str().unwrap().contains("c.out"));
        assert_eq!(
            item["locations"][0]["physicalLocation"]["region"]["startColumn"],
            source.find("c=Leaf()").unwrap() + 3
        );
        fs::remove_file(&path).unwrap();
    });
}

#[test]
fn unavailable_outputless_input_child_withholds_unused_output_warning() {
    for (body, parent) in [
        ("x===1;", "component e=Empty();"),
        ("x===1;", "component e=Empty();e.x<==1;e.x<==1;"),
        ("x===1;", "component e=Empty();e.x<--1;"),
        ("x===1;assert(0);", "component e=Empty();e.x<==1;"),
        ("x===1;var bad=1/0;", "component e=Empty();e.x<==1;"),
        ("x===1;", "component e[1];e[0]=Empty();e[1].x<==1;"),
        ("x===1;", "signal input i;component e[1];e[0]=Empty();e[i].x<==1;"),
    ] {
        let source = format!(
            "template Leaf(){{signal output out;out<==1;}}\
             template Empty(){{signal input x;{body}}}\
             template Parent(){{component c=Leaf();{parent}}}component main=Parent();"
        );
        run_case(&source, "Parent", |results, _| {
            assert_eq!(count(results, RuleKind::UnusedOutputSignal), 0, "{source}");
            assert!(
                results.abstentions().iter().any(|item| item.kind == RuleKind::UnusedOutputSignal),
                "{source}"
            );
        });
    }
}

#[test]
fn pure_dead_assignment_emits_cs0008_and_a_returned_value_does_not() {
    run_case("function Check(){var x=1;return 7;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 1);
    });
    run_case("function Check(){var x=1;return x;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 0);
    });
}

#[test]
fn dead_scalar_chain_emits_two_cs0008_findings_at_assignment_sources() {
    let source = "function Check(){var x=1;var y=x;return 7;}";
    run_case(source, "Check", |results, sources| {
        let findings: Vec<_> = results
            .findings()
            .iter()
            .filter(|finding| finding.kind() == RuleKind::SideEffectFreeAssignment)
            .cloned()
            .collect();
        assert_eq!(findings.len(), 2);
        assert_eq!(count(results, RuleKind::UnusedVariableValue), 1);
        let path = std::env::temp_dir().join(format!(
            "circomspect-dead-chain-{}-{:?}.json",
            std::process::id(),
            std::thread::current().id()
        ));
        assert_eq!(
            support::render(&findings, sources, MessageCategory::Warning, &[], &path).unwrap(),
            (2, 2)
        );
        let sarif: serde_json::Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        let results = sarif["runs"][0]["results"].as_array().unwrap();
        let columns: Vec<_> = results
            .iter()
            .map(|result| {
                assert_eq!(result["ruleId"], "CS0008");
                assert_eq!(result["level"], "warning");
                assert_eq!(result["locations"][0]["physicalLocation"]["region"]["startLine"], 1);
                usize::try_from(
                    result["locations"][0]["physicalLocation"]["region"]["startColumn"]
                        .as_u64()
                        .unwrap(),
                )
                .unwrap()
            })
            .collect();
        assert_eq!(columns, vec![source.find("x=1").unwrap() + 1, source.find("y=x").unwrap() + 1]);
        assert_eq!(
            support::render(&findings, sources, MessageCategory::Warning, &["CS0008"], &path)
                .unwrap(),
            (0, 0)
        );
    });
}

#[test]
fn observed_scalar_chain_keeps_both_assignments_and_syntactic_reads() {
    for source in [
        "function Check(){var x=1;var y=x;return y;}",
        "function Check(){var x=1;var y=x;assert(y);return 7;}",
        "template Check(){var x=1;var y=x;signal output z;z<==y;}",
    ] {
        run_case(source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 0, "{source}");
            assert_eq!(count(results, RuleKind::UnusedVariableValue), 0, "{source}");
        });
    }
}

#[test]
fn unsafe_or_unknown_chain_rhs_cannot_be_reported_removable() {
    for source in [
        "function Child(){assert(1);return 7;}function Check(){var x=Child();return 7;}",
        "template Check(){signal input s;var x=s;}",
        "function Check(i){var a[2];var x=a[i];return 7;}",
        "function Check(){var x=Missing();return 7;}",
    ] {
        run_case(source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 0, "{source}");
            assert!(
                results
                    .abstentions()
                    .iter()
                    .any(|abstention| { abstention.kind == RuleKind::SideEffectFreeAssignment }),
                "{source}"
            );
        });
    }
}

#[test]
fn side_effect_free_assignment_uses_only_a_pure_dead_scalar_value() {
    for (source, expected) in [
        ("function Check(){var x=1;return 7;}", 1),
        ("function Check(){var a=1;var x=a;return a;}", 1),
        ("function Check(){var x=1;return x;}", 0),
        ("function Check(){var x=1;x=2;return x;}", 1),
        ("function Check(p){var x=p;return x;}", 0),
        ("function Check(p){var x=p;return 7;}", 0),
        ("function Check(){var x=1+2;return 7;}", 1),
    ] {
        run_case(source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), expected, "{source}");
        });
    }
    run_case("function Check(p){var x=p;return 7;}", "Check", |results, _| {
        assert!(results
            .abstentions()
            .iter()
            .any(|abstention| { abstention.kind == RuleKind::SideEffectFreeAssignment }));
    });
}

#[test]
fn exact_dead_arithmetic_uses_shared_evaluation_evidence() {
    for (source, expected) in [
        ("function Check(){var x=1+2;return 7;}", 1),
        ("function Check(){var a=2;var x=-(a+3)*4;return 7;}", 2),
        ("function Check(){var x=!0;return 7;}", 1),
        ("function Check(){var x=2<3;return 7;}", 1),
        ("function Check(){var a=2;var x=-(a+3)*4;return x;}", 0),
        ("template Check(p){var x=-p+2;}component main=Check(3);", 1),
        ("template Check(p){var x=p;}component main=Check(3);", 1),
    ] {
        run_case(source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), expected, "{source}");
        });
    }
}

#[test]
fn unsafe_dead_arithmetic_keeps_failure_read_and_call_safeguards() {
    for source in [
        "function Check(){var x=1/0;return 7;}",
        "function Check(p){var x=p+1;return 7;}",
        "function Check(){var a[2];var x=a[2]+1;return 7;}",
        "function Check(i){var a[2];var x=a[i]+1;return 7;}",
        "template Check(){signal s;var x=s+1;s<==2;}",
        "function Check(){var x=Missing()+1;return 7;}",
        "function Noisy(){log(1);return 7;}function Check(){var x=Noisy()+1;return 7;}",
        "function Bad(){assert(0);return 7;}function Check(){var x=Bad()+1;return 7;}",
    ] {
        run_case(source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 0, "{source}");
            assert!(
                results
                    .abstentions()
                    .iter()
                    .any(|abstention| { abstention.kind == RuleKind::SideEffectFreeAssignment }),
                "{source}"
            );
        });
    }
}

#[test]
fn pure_dead_local_assignment_retains_both_defined_rule_claims() {
    for rhs in ["1", "1+2"] {
        let source = format!("function Check(){{var x={rhs};return 7;}}");
        run_case(&source, "Check", |results, sources| {
            let findings: Vec<_> = results
                .findings()
                .iter()
                .filter(|finding| {
                    finding.kind() == RuleKind::SideEffectFreeAssignment
                        || finding.kind() == RuleKind::UnusedVariableValue
                })
                .cloned()
                .collect();
            assert_eq!(findings.len(), 2);
            let path = std::env::temp_dir().join(format!(
                "circomspect-use-overlap-{}-{:?}.json",
                std::process::id(),
                std::thread::current().id()
            ));
            assert_eq!(
                support::render(&findings, sources, MessageCategory::Warning, &[], &path).unwrap(),
                (2, 2)
            );
            let sarif: serde_json::Value =
                serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
            let locations = &sarif["runs"][0]["results"];
            let first = &locations[0]["locations"][0]["physicalLocation"]["region"];
            let second = &locations[1]["locations"][0]["physicalLocation"]["region"];
            assert_eq!(first, second);
        });
    }
}

#[test]
fn unused_local_value_and_internal_signal_emit_cs0006() {
    run_case("function Check(){var x=1;x=2;return x;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedVariableValue), 1);
    });
    run_case("template Check(){signal x;x<--7;signal output y;y<==1;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedVariableValue), 1);
    });
    run_case("template Check(){signal output x;x<--7;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedVariableValue), 0);
    });
}

#[test]
fn unused_value_respects_overwrite_and_export_boundaries() {
    for (source, expected) in [
        ("function Check(){var x=1;x=2;return x;}", 1),
        ("function Check(){var x=1;return x;}", 0),
        ("function Check(){var x=1;x=2;return 7;}", 2),
        ("template Check(){signal x;x<--7;}", 1),
        ("template Check(){signal output x;x<--7;}", 0),
        ("template Check(){signal input x;signal output y;y<==x;}", 0),
    ] {
        run_case(source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::UnusedVariableValue), expected, "{source}");
        });
    }
}

#[test]
fn symbolic_signal_index_and_constraint_are_may_uses_of_internal_values() {
    let source = concat!(
        "template Check(){signal input i;signal x[2];x[0]<--1;",
        "signal output y;y<==x[i];}"
    );
    run_case(source, "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedVariableValue), 0);
    });
}

#[test]
fn failing_or_custom_template_cannot_certify_an_unused_internal_signal() {
    for source in [
        "template Check(){assert(0);signal s;s<--1;}",
        "pragma custom_templates; template custom Check(){signal s;s<--1;}",
    ] {
        run_case(source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::UnusedVariableValue), 0, "{source}");
            assert!(results
                .abstentions()
                .iter()
                .any(|abstention| { abstention.kind == RuleKind::UnusedVariableValue }));
        });
    }
    run_case("template Check(){assert(1);signal s;s<--1;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedVariableValue), 1);
    });
}

#[test]
fn reading_an_uninitialized_signal_is_not_a_side_effect_free_assignment() {
    let source = "template Check(){signal output s;var x=s;s<==1;}";
    run_case(source, "Check", |results, _| {
        assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 0);
    });
}

#[test]
fn assignment_after_a_failing_assertion_has_no_executed_unused_value() {
    for source in [
        "function Check(){assert(0);var x=1;return 7;}",
        "function Check(){var z=1/0;var x=1;return 7;}",
        "template Check(){if(1){assert(0);}var x=1;}",
    ] {
        run_case(source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::UnusedVariableValue), 0, "{source}");
            assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 0, "{source}");
            let reason =
                AbstentionReason::Summary(BTreeSet::from([SummaryBlocker::UnsupportedContext]));
            assert!(results.abstentions().iter().any(|abstention| {
                abstention.kind == RuleKind::UnusedVariableValue && abstention.reason == reason
            }));
        });
    }
    run_case("function Check(){assert(1);var x=1;return 7;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedVariableValue), 1);
        assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 1);
    });
    run_case("function Check(){if(0){assert(0);}var x=1;return 7;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedVariableValue), 1);
        assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 1);
    });
    run_case("function Check(p){assert(0);return 7;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedParameterValue), 0);
    });
}

#[test]
fn unresolved_symbolic_value_keeps_unused_value_claim_incomplete() {
    run_case("template Check(n){var x=~n;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedVariableValue), 0);
        assert!(results.abstentions().iter().any(|abstention| {
            abstention.kind == RuleKind::UnusedVariableValue
                && abstention.reason == AbstentionReason::IncompleteDefinition
        }));
    });
}

#[test]
fn unread_validated_parameter_emits_cs0007_but_any_reachable_read_suppresses_it() {
    run_case("function Check(p){return 7;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedParameterValue), 1);
    });
    run_case("function Check(p){return p;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedParameterValue), 0);
    });
    run_case("function Check(p){if(0){return p;}return 7;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedParameterValue), 1);
    });
}

#[test]
fn parameter_read_paths_never_become_false_unread_proofs() {
    for (source, expected) in [
        ("function Check(p){return 7;}", 1),
        ("function Check(p){return p;}", 0),
        ("function Check(p){p=1;return p;}", 0),
        ("function Check(p){return p[0];}", 0),
        ("function Check(p){assert(p);return 7;}", 0),
        ("function Check(p){if(p){return 1;}return 7;}", 0),
        ("function Check(p){if(0){return p;}return 7;}", 1),
        ("function Child(q){return q;}function Check(p){var x=Child(p);return 7;}", 0),
    ] {
        run_case(source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::UnusedParameterValue), expected, "{source}");
        });
    }
}

#[test]
fn closed_main_unused_exact_child_output_emits_cs0018_and_library_abstains() {
    let body = concat!(
        "template Child(){signal output a;signal output b;a<==1;b<==2;} ",
        "template Parent(){component c=Child();signal output y;y<==c.a;}"
    );
    let main = format!("{body} component main=Parent();");
    run_case(&main, "Parent", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedOutputSignal), 1);
    });
    run_case(body, "Parent", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedOutputSignal), 0);
        assert!(results
            .abstentions()
            .iter()
            .any(|abstention| { abstention.kind == RuleKind::UnusedOutputSignal }));
    });
}

#[test]
fn exact_output_array_reads_report_only_unread_indices() {
    let source = concat!(
        "template Child(){signal output out[2];out[0]<==1;out[1]<==2;} ",
        "template Parent(){component c=Child();signal output y;y<==c.out[0];}",
        "component main=Parent();"
    );
    run_case(source, "Parent", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedOutputSignal), 1);
    });
}

#[test]
fn component_array_reads_report_only_unread_instance_outputs() {
    let source = concat!(
        "template Child(){signal output out;out<==1;} ",
        "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
        "signal output y;y<==c[0].out;} component main=Parent();"
    );
    run_case(source, "Parent", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedOutputSignal), 1);
    });
}

#[test]
fn symbolic_output_index_is_a_may_read_for_every_exact_element() {
    let source = concat!(
        "template Child(){signal output out[2];out[0]<==1;out[1]<==2;} ",
        "template Parent(){signal input i;component c=Child();",
        "signal output y;y<==c.out[i];} component main=Parent();"
    );
    run_case(source, "Parent", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedOutputSignal), 0);
    });
}

#[test]
fn unknown_child_and_incomplete_local_scope_abstain_without_output_warning() {
    let source = concat!(
        "template Child(){signal output out;out<==1;} ",
        "template Parent(){component c=Child();component d=Missing();} ",
        "component main=Parent();"
    );
    run_case(source, "Parent", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedOutputSignal), 0);
        assert!(results
            .abstentions()
            .iter()
            .any(|abstention| { abstention.kind == RuleKind::UnusedOutputSignal }));
    });
}

#[test]
fn output_enumeration_cap_abstains_instead_of_reporting_a_partial_prefix() {
    let mut source = String::from("template Child(){signal output out[16];} template Parent(){");
    for index in 0..17 {
        source.push_str(&format!("component c{index}=Child();"));
    }
    source.push_str("} component main=Parent();");
    run_case(&source, "Parent", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedOutputSignal), 0);
        assert!(results
            .abstentions()
            .iter()
            .any(|abstention| { abstention.kind == RuleKind::UnusedOutputSignal }));
    });
}

#[test]
fn invalid_unrelated_library_definition_does_not_hide_unread_parameter() {
    let source =
        concat!("function Broken(){var x=Missing();return 7;} ", "function Check(p){return 7;}");
    run_case(source, "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedParameterValue), 1);
    });
}

#[test]
fn incomplete_local_definition_does_not_emit_unread_parameter() {
    run_case("function Check(p){var x=Missing();return 7;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedParameterValue), 0);
        assert!(results
            .abstentions()
            .iter()
            .any(|abstention| { abstention.kind == RuleKind::UnusedParameterValue }));
    });
}

#[test]
fn every_use_rule_keeps_its_id_severity_span_and_allow_filter() {
    let cases = [
        (
            "function Check(){var x=1;return 7;}",
            "Check",
            RuleKind::SideEffectFreeAssignment,
            "CS0008",
            "x=1",
        ),
        (
            "template Check(){signal x;x<--7;}",
            "Check",
            RuleKind::UnusedVariableValue,
            "CS0006",
            "x<--7",
        ),
        ("function Check(p){return 7;}", "Check", RuleKind::UnusedParameterValue, "CS0007", "p){"),
        (
            concat!(
                "template Child(){signal output a;signal output b;a<==1;b<==2;} ",
                "template Parent(){component c=Child();signal output y;y<==c.a;} ",
                "component main=Parent();"
            ),
            "Parent",
            RuleKind::UnusedOutputSignal,
            "CS0018",
            "Child();signal",
        ),
    ];
    for (source, definition, kind, code, marker) in cases {
        run_case(source, definition, |results, sources| {
            let findings: Vec<_> = results
                .findings()
                .iter()
                .filter(|finding| finding.kind() == kind)
                .cloned()
                .collect();
            assert_eq!(findings.len(), 1, "{code}");
            let path = std::env::temp_dir().join(format!(
                "circomspect-use-rule-{}-{}-{:?}.json",
                std::process::id(),
                code,
                std::thread::current().id()
            ));
            let rendered =
                support::render(&findings, sources, MessageCategory::Warning, &[], &path).unwrap();
            assert_eq!(rendered, (1, 1), "{code}");
            let sarif: serde_json::Value =
                serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
            let result = &sarif["runs"][0]["results"][0];
            assert_eq!(result["ruleId"], code);
            assert_eq!(result["level"], "warning");
            let location = &result["locations"][0]["physicalLocation"];
            assert_eq!(location["region"]["startLine"], 1);
            assert_eq!(location["region"]["startColumn"], source.find(marker).unwrap() + 1);
            assert_eq!(
                support::render(&findings, sources, MessageCategory::Warning, &[code], &path)
                    .unwrap(),
                (0, 0),
                "{code}"
            );
        });
    }
}

#[test]
fn independent_signal_reads_are_never_classified_as_pure_dead_copies() {
    for source in [
        "template Check(){signal output s;var x=s;s<==1;}",
        "template Check(){signal output s;s<==1;var x=s;}",
        "template Check(){signal input s;var x=s;}",
        "template Child(){signal output s;s<==1;}template Check(){component c=Child();var x=c.s;}",
    ] {
        run_case(source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 0, "{source}");
        });
    }
    run_case("function Check(){var a=1;var x=a;return a;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 1);
    });
}

#[test]
fn independent_internal_signal_guards_cover_external_bodies_and_bounds() {
    for source in [
        "pragma custom_templates;template custom Check(){signal s;s<--1;}",
        "template extern_c Check(){signal s;s<--1;}",
        "template Check(){signal s[0];s[0]<--1;}",
        "template Check(){signal s[1];s[1]<--1;}",
        "template Check(){assert(0);signal s;s<--1;}",
    ] {
        run_case(source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::UnusedVariableValue), 0, "{source}");
        });
    }
    run_case("template Check(){signal s[1];s[0]<--1;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedVariableValue), 1);
    });
}

#[test]
fn dead_assignments_do_not_create_incomplete_analysis() {
    for source in [
        "function Check(){if(0){var x=1;}return 7;}",
        "function F(){return 7;}function Check(){if(0){var x=F();}return 7;}",
    ] {
        run_case(source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 0, "{source}");
            assert!(
                !results
                    .abstentions()
                    .iter()
                    .any(|item| item.kind == RuleKind::SideEffectFreeAssignment),
                "dead source must not produce an incomplete scope: {source}"
            );
        });
    }
}

#[test]
fn dead_chains_in_a_partial_library_keep_exact_findings() {
    let source = "function Broken(){return Missing();}function Check(){var x=1;var y=x;return 7;}";
    run_case(source, "Check", |results, _| {
        assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 2);
    });
}

#[test]
fn dead_known_call_is_quiet_and_independent_assignment_still_warns() {
    let source =
        concat!("function F(){return 7;}", "function Check(){if(0){var x=F();}var y=1;return 7;}");
    run_case(source, "Check", |results, sources| {
        let findings: Vec<_> = results
            .findings()
            .iter()
            .filter(|item| item.kind() == RuleKind::SideEffectFreeAssignment)
            .cloned()
            .collect();
        assert_eq!(findings.len(), 1);
        let path = std::env::temp_dir().join(format!(
            "circomspect-dead-known-call-{}-{:?}.json",
            std::process::id(),
            std::thread::current().id()
        ));
        assert_eq!(
            support::render(&findings, sources, MessageCategory::Warning, &[], &path).unwrap(),
            (1, 1)
        );
        let sarif: serde_json::Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        assert_eq!(
            sarif["runs"][0]["results"][0]["locations"][0]["physicalLocation"]["region"]
                ["startColumn"],
            source.find("y=1").unwrap() + 1
        );
        assert!(!results
            .abstentions()
            .iter()
            .any(|item| { item.kind == RuleKind::SideEffectFreeAssignment }));
    });
}

#[test]
fn dead_pure_call_chain_emits_cs0008_at_both_assignment_sources() {
    let source =
        concat!("function Pure(n){return n;}", "function Check(){var x=1;var y=Pure(x);return 7;}");
    run_case(source, "Check", |results, sources| {
        let findings: Vec<_> = results
            .findings()
            .iter()
            .filter(|item| item.kind() == RuleKind::SideEffectFreeAssignment)
            .cloned()
            .collect();
        assert_eq!(findings.len(), 2);
        assert_eq!(count(results, RuleKind::UnusedVariableValue), 1);
        let path = std::env::temp_dir().join(format!(
            "circomspect-pure-call-chain-{}-{:?}.json",
            std::process::id(),
            std::thread::current().id()
        ));
        assert_eq!(
            support::render(&findings, sources, MessageCategory::Warning, &[], &path).unwrap(),
            (2, 2)
        );
        let sarif: serde_json::Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        let items = sarif["runs"][0]["results"].as_array().unwrap();
        let columns: Vec<_> = items
            .iter()
            .map(|item| {
                assert_eq!(item["ruleId"], "CS0008");
                assert_eq!(item["level"], "warning");
                usize::try_from(
                    item["locations"][0]["physicalLocation"]["region"]["startColumn"]
                        .as_u64()
                        .unwrap(),
                )
                .unwrap()
            })
            .collect();
        assert_eq!(
            columns,
            vec![source.find("x=1").unwrap() + 1, source.find("y=Pure").unwrap() + 1]
        );
        assert_eq!(
            support::render(&findings, sources, MessageCategory::Warning, &["CS0008"], &path)
                .unwrap(),
            (0, 0)
        );
    });
}

#[test]
fn resolved_call_results_use_syntactic_liveness_for_cs0006() {
    for (body, expected) in [
        ("var y=Pure();return 1;", 1),
        ("var y=Pure();return y;", 0),
        ("var y=Pure();y=1;return y;", 1),
        ("var y=Pure();var z=y;return 1;", 1),
    ] {
        let source = format!("function Pure(){{return 7;}}function Check(){{{body}}}");
        run_case(&source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::UnusedVariableValue), expected, "{source}");
        });
    }
}

#[test]
fn unused_call_result_retains_all_evaluated_argument_reads() {
    for callee in ["function Pure(a,b){return 7;}", "function Pure(a,b){log(a);return b;}"] {
        let source = format!(
            "{callee}function Inner(a){{return 2;}}\
             function Check(){{var x=1;var z=2;var y=Pure(x,Inner(z));return 7;}}"
        );
        run_case(&source, "Check", |results, sources| {
            let findings: Vec<_> = results
                .findings()
                .iter()
                .filter(|finding| finding.kind() == RuleKind::UnusedVariableValue)
                .collect();
            assert_eq!(findings.len(), 1, "{source}");
            assert!(findings[0].to_report(sources).unwrap().message().contains("`y`"));
        });
    }
}

#[test]
fn unresolved_or_invalid_calls_withhold_unused_assigned_values() {
    for callee in ["", "function Pure(){assert(0);return 7;}", "function Pure(){return Missing();}"]
    {
        let source = format!("{callee}function Check(){{var y=Pure();return 1;}}");
        run_case(&source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::UnusedVariableValue), 0, "{source}");
            assert!(
                results
                    .abstentions()
                    .iter()
                    .any(|abstention| { abstention.kind == RuleKind::UnusedVariableValue }),
                "{source}"
            );
        });
    }
}

#[test]
fn nested_pure_call_result_is_removable_but_observed_result_keeps_argument_chain() {
    run_case(
        "function Pure(n){return n;}function Inner(){return 1;}\
         function Check(){var y=Pure(Inner());return 7;}",
        "Check",
        |results, _| assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 1),
    );
    run_case(
        "function Pure(){return 7;}template Check(){var y=Pure();}component main=Check();",
        "Check",
        |results, _| assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 1),
    );
    for observation in ["return y;", "assert(y);return 7;"] {
        let source = format!(
            "function Pure(n){{return 7;}}\
             function Check(){{var x=1;var y=Pure(x);{observation}}}"
        );
        run_case(&source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 0, "{source}");
        });
    }
}

#[test]
fn nested_unused_array_output_preserves_full_instance_path_and_sarif_location() {
    let source = concat!(
        "template Leaf(){signal output out[2];out[0]<==1;out[1]<==2;} ",
        "template Middle(){component c=Leaf();signal output y;y<==c.out[0];} ",
        "template Parent(){component m=Middle();signal output z;z<==m.y;} ",
        "component main=Parent();"
    );
    run_case(source, "Parent", |results, sources| {
        let findings: Vec<_> = results
            .findings()
            .iter()
            .filter(|item| item.kind() == RuleKind::UnusedOutputSignal)
            .cloned()
            .collect();
        assert_eq!(findings.len(), 1);
        let path = std::env::temp_dir().join(format!(
            "circomspect-nested-output-{}-{:?}.json",
            std::process::id(),
            std::thread::current().id()
        ));
        assert_eq!(
            support::render(&findings, sources, MessageCategory::Warning, &[], &path).unwrap(),
            (1, 1)
        );
        let sarif: serde_json::Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        let item = &sarif["runs"][0]["results"][0];
        assert_eq!(item["ruleId"], "CS0018");
        assert_eq!(item["level"], "warning");
        assert!(item["message"]["text"].as_str().unwrap().contains("m.c.out[1]"));
        assert_eq!(item["relatedLocations"][0]["message"]["text"], "instance `m`");
        assert_eq!(
            item["relatedLocations"][0]["physicalLocation"]["region"]["startColumn"],
            source.find("m=Middle()").unwrap() + "m=".len() + 1
        );
        assert_eq!(
            item["locations"][0]["physicalLocation"]["region"]["startColumn"],
            source.find("c=Leaf()").unwrap() + 3
        );
        assert_eq!(
            support::render(&findings, sources, MessageCategory::Warning, &["CS0018"], &path)
                .unwrap(),
            (0, 0)
        );
        fs::remove_file(&path).unwrap();
    });
}

#[test]
fn equal_nested_source_sites_keep_distinct_rooted_instance_warnings() {
    let source = concat!(
        "template Leaf(){signal output a;signal output b;a<==1;b<==2;} ",
        "template Middle(){component c=Leaf();signal output y;y<==c.a;} ",
        "template Parent(){component m[2];m[0]=Middle();m[1]=Middle();",
        "signal output z;z<==m[0].y;}component main=Parent();"
    );
    run_case(source, "Parent", |results, sources| {
        let findings: Vec<_> = results
            .findings()
            .iter()
            .filter(|item| item.kind() == RuleKind::UnusedOutputSignal)
            .cloned()
            .collect();
        assert_eq!(findings.len(), 3);
        let path = std::env::temp_dir().join(format!(
            "circomspect-nested-instances-{}-{:?}.json",
            std::process::id(),
            std::thread::current().id()
        ));
        assert_eq!(
            support::render(&findings, sources, MessageCategory::Warning, &[], &path).unwrap(),
            (3, 3)
        );
        let sarif: serde_json::Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        let items = sarif["runs"][0]["results"].as_array().unwrap();
        let messages: Vec<_> =
            items.iter().map(|item| item["message"]["text"].as_str().unwrap()).collect();
        assert!(messages.iter().any(|message| message.contains("m[0].c.b")));
        assert!(messages.iter().any(|message| message.contains("m[1].c.b")));
        assert!(messages.iter().any(|message| message.contains("m[1].y")));
        for (index, label) in ["m[0]", "m[1]"].iter().enumerate() {
            let item = items
                .iter()
                .find(|item| {
                    item["message"]["text"].as_str().unwrap().contains(&format!("{label}.c.b"))
                })
                .unwrap();
            assert_eq!(
                item["relatedLocations"][0]["message"]["text"],
                format!("instance `{label}`")
            );
            assert_eq!(
                item["relatedLocations"][0]["physicalLocation"]["region"]["startColumn"],
                source.find(&format!("m[{index}]=Middle()")).unwrap() + "m[0]=".len() + 1
            );
            assert_eq!(
                item["locations"][0]["physicalLocation"]["region"]["startColumn"],
                source.find("c=Leaf()").unwrap() + "c=".len() + 1
            );
        }
        fs::remove_file(&path).unwrap();
    });
}

#[test]
fn complete_reads_of_nested_output_elements_do_not_emit_unused_warning() {
    let source = concat!(
        "template Leaf(){signal output out[2];out[0]<==1;out[1]<==2;} ",
        "template Middle(){component c=Leaf();signal output y[2];",
        "y[0]<==c.out[0];y[1]<==c.out[1];} ",
        "template Parent(){component m=Middle();signal output z[2];",
        "z[0]<==m.y[0];z[1]<==m.y[1];}component main=Parent();"
    );
    run_case(source, "Parent", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedOutputSignal), 0);
    });
}

#[test]
fn use_corpus_replays_each_declared_scope_and_outcome() {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().join("tests/warnings");
    let manifest: serde_json::Value =
        serde_json::from_slice(&fs::read(root.join("manifest.json")).unwrap()).unwrap();
    let mut checked = 0;
    for case in manifest["cases"].as_array().unwrap() {
        let kind = if case["rule"] == "side_effect_free_assignment" {
            RuleKind::SideEffectFreeAssignment
        } else if case["rule"] == "unused_output" {
            RuleKind::UnusedOutputSignal
        } else {
            continue;
        };
        let source = fs::read_to_string(root.join(case["source"].as_str().unwrap())).unwrap();
        run_case(&source, case["scope"].as_str().unwrap(), |results, _| {
            let findings = count(results, kind);
            let abstained = results.abstentions().iter().any(|item| item.kind == kind);
            match case["expected"].as_str().unwrap() {
                "emit" => assert_eq!(findings, 1, "{case}"),
                "no_finding" => assert_eq!(findings, 0, "{case}"),
                "abstain" => {
                    assert_eq!(findings, 0, "{case}");
                    assert!(abstained, "{case}");
                }
                outcome => panic!("unexpected corpus outcome: {outcome}"),
            }
        });
        checked += 1;
    }
    assert_eq!(checked, 6);
}

#[test]
fn pure_calls_reuse_certified_arithmetic_argument_safety() {
    for (body, expected) in [
        ("function Check(){var y=Pure(1+2);return 7;}", 1),
        ("function Check(){var y=Pure(2**3);return 7;}", 1),
        ("function Check(){var x=2;var y=Pure(-(x+1));return 7;}", 2),
        ("function Check(){var y=Pure(Inner()+1);return 7;}", 1),
        ("function Check(){var y=Pure(1+2)+4;return 7;}", 1),
        ("function Check(){var x=2;var y=Pure(x+1);return y;}", 0),
        ("template Check(p){var y=Pure(-p+1);}component main=Check(3);", 1),
        ("template Check(p){var y=Pure(p);}component main=Check(3);", 1),
    ] {
        let source = format!("function Pure(n){{return n;}}function Inner(){{return 2;}}{body}");
        run_case(&source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), expected, "{source}");
        });
    }
}

#[test]
fn arithmetic_arguments_retain_nested_call_effects_and_failures() {
    for source in [
        "function Noisy(){log(1);return 2;}function Check(){var y=Pure(Noisy()+1);return 7;}",
        "function Noisy(){log(1);return 2;}function Check(){var y=Pure(0*Noisy());return 7;}",
        "function Bad(){assert(0);return 2;}function Check(){var y=Pure(Bad()+1);return 7;}",
        "function Check(){var y=Pure(Missing()+1);return 7;}",
        "function Check(){var y=Pure(1/0);return 7;}",
        "function Check(){var y=Pure(2**513);return 7;}",
        "function Check(p){var y=Pure(p+1);return 7;}",
        "template Check(p){var y=Pure(p);}",
        "template Check(){signal s;var y=Pure(s+1);s<==2;}",
    ] {
        let source = format!("function Pure(n){{return n;}}{source}");
        run_case(&source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 0, "{source}");
            assert!(
                results
                    .abstentions()
                    .iter()
                    .any(|item| { item.kind == RuleKind::SideEffectFreeAssignment }),
                "{source}"
            );
        });
    }
}

#[test]
fn opaque_sibling_and_budget_exhaustion_withhold_nested_unused_warnings() {
    let opaque = concat!(
        "template Leaf(){signal output out;out<==1;} ",
        "template Parent(){component c=Leaf();component missing=Missing();} ",
        "component main=Parent();"
    );
    run_case(opaque, "Parent", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedOutputSignal), 0);
        assert!(results.abstentions().iter().any(|item| item.kind == RuleKind::UnusedOutputSignal));
    });
    let budget = concat!(
        "template Leaf(){signal output out[256];} ",
        "template Parent(){component c=Leaf();}component main=Parent();"
    );
    run_case(budget, "Parent", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedOutputSignal), 0);
        assert!(results.abstentions().iter().any(|item| {
            item.kind == RuleKind::UnusedOutputSignal
                && if let AbstentionReason::Summary(blockers) = &item.reason {
                    blockers.contains(&SummaryBlocker::ContextBudget)
                } else {
                    false
                }
        }));
    });
}

#[test]
fn uninstantiated_library_output_never_becomes_a_project_unused_warning() {
    let source = concat!(
        "template Leaf(){signal output out;out<==1;} ",
        "template Parent(){component c=Leaf();}"
    );
    run_case(source, "Parent", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedOutputSignal), 0);
        assert!(results.abstentions().iter().any(|item| item.kind == RuleKind::UnusedOutputSignal));
    });
}

#[test]
fn impure_or_unproven_calls_keep_cs0008_unavailable() {
    for source in [
        "function Loggy(){log(1);return 7;}function Check(){var y=Loggy();return 7;}",
        "function Loggy(){log(1);return 2;}function Pure(n){return 7;}\
         function Check(){var y=Pure(Loggy());return 7;}",
        "function F(){return F();}function Check(){var y=F();return 7;}",
        "function Bad(n,n){return 7;}function Check(){var y=Bad(1,2);return 7;}",
    ] {
        run_case(source, "Check", |results, _| {
            assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 0, "{source}");
            assert!(
                results
                    .abstentions()
                    .iter()
                    .any(|item| { item.kind == RuleKind::SideEffectFreeAssignment }),
                "{source}"
            );
        });
    }
}

#[test]
fn three_level_output_warning_retains_every_ancestor_location() {
    let source = concat!(
        "template Leaf(){signal output out;out<==1;}",
        "template Middle(){component leaf=Leaf();}",
        "template Outer(){component mid=Middle();}",
        "template Parent(){component top=Outer();}component main=Parent();"
    );
    run_case(source, "Parent", |results, sources| {
        let findings: Vec<_> = results
            .findings()
            .iter()
            .filter(|finding| finding.kind() == RuleKind::UnusedOutputSignal)
            .collect();
        assert_eq!(findings.len(), 1);
        let report = findings[0].to_report(sources).unwrap();
        assert!(report.message().contains("top.mid.leaf.out"));
        assert_eq!(report.secondary().len(), 2);
        assert_eq!(
            report.secondary()[0].range.start,
            source.find("top=Outer()").unwrap() + "top=".len()
        );
        assert_eq!(
            report.secondary()[1].range.start,
            source.find("mid=Middle()").unwrap() + "mid=".len()
        );
    });
}

#[test]
fn overwrites_and_zero_coefficient_arguments_preserve_source_reads() {
    for (body, unused) in [
        ("var x=2;var y=Pure(0*x);return 7;", "y"),
        ("var x=2;var y=Pure(x);y=5;return y;", "y"),
        ("var x=2;var y=Pure(x);return 0*y;", ""),
    ] {
        let source = format!("function Pure(n){{return 7;}}function Check(){{{body}}}");
        run_case(&source, "Check", |results, sources| {
            let findings: Vec<_> = results
                .findings()
                .iter()
                .filter(|finding| finding.kind() == RuleKind::UnusedVariableValue)
                .collect();
            if unused.is_empty() {
                assert!(findings.is_empty(), "{source}");
            } else {
                assert_eq!(findings.len(), 1, "{source}");
                assert!(findings[0].to_report(sources).unwrap().message().contains("`y`"));
            }
        });
    }
}

#[test]
fn all_outputless_child_inputs_need_valid_unique_generated_bindings() {
    for (bindings, emits) in [
        ("e.x<==1;e.y<==2;", true),
        ("e.x<==1;", false),
        ("e.x<==1;e.y<--2;", false),
        ("e.x<==1;e.y<==2;e.x<==1;", false),
    ] {
        let source = format!(
            "template Leaf(){{signal output out;out<==1;}}\
             template Empty(){{signal input x;signal input y;x===1;y===2;}}\
             template Parent(){{component c=Leaf();component e=Empty();{bindings}}}\
             component main=Parent();"
        );
        run_case(&source, "Parent", |results, _| {
            assert_eq!(
                count(results, RuleKind::UnusedOutputSignal),
                usize::from(emits),
                "{source}"
            );
            if !emits {
                assert!(
                    results
                        .abstentions()
                        .iter()
                        .any(|item| item.kind == RuleKind::UnusedOutputSignal),
                    "{source}"
                );
            }
        });
    }
}
