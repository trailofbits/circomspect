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
                result["locations"][0]["physicalLocation"]["region"]["startColumn"]
                    .as_u64()
                    .unwrap() as usize
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
        ("function Check(){var x=1+2;return 7;}", 0),
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
    run_case("function Check(){var x=1+2;return 7;}", "Check", |results, _| {
        assert!(results
            .abstentions()
            .iter()
            .any(|abstention| { abstention.kind == RuleKind::SideEffectFreeAssignment }));
    });
}

#[test]
fn pure_dead_local_assignment_retains_both_defined_rule_claims() {
    run_case("function Check(){var x=1;return 7;}", "Check", |results, sources| {
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
        let sarif: serde_json::Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        let locations = &sarif["runs"][0]["results"];
        let first = &locations[0]["locations"][0]["physicalLocation"]["region"];
        let second = &locations[1]["locations"][0]["physicalLocation"]["region"];
        assert_eq!(first, second);
    });
}

#[test]
fn unused_local_value_and_internal_signal_emit_cs0006() {
    run_case("function Check(){var x=1;x=2;return x;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedVariableValue), 1);
    });
    run_case("template Check(){signal x;x<--7;signal output y;y<==1;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedVariableValue), 1)
    });
    run_case("template Check(){signal output x;x<--7;}", "Check", |results, _| {
        assert_eq!(count(results, RuleKind::UnusedVariableValue), 0)
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
fn dead_plain_assignment_does_not_create_incomplete_analysis() {
    let source = "function Check(){if(0){var x=1;}return 7;}";
    run_case(source, "Check", |results, _| {
        assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 0);
        assert!(!results
            .abstentions()
            .iter()
            .any(|item| { item.kind == RuleKind::SideEffectFreeAssignment }));
    });
}

#[test]
fn dead_chains_in_a_partial_library_keep_exact_findings() {
    let source = "function Broken(){return Missing();}function Check(){var x=1;var y=x;return 7;}";
    run_case(source, "Check", |results, _| {
        assert_eq!(count(results, RuleKind::SideEffectFreeAssignment), 2);
    });
}
