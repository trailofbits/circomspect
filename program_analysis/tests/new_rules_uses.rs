mod support;

use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::interprocedural::{CallOwner, CallReachability, ProjectSummaries};
use circomspect_program_analysis::new_rules::{
    run_registered, RuleContext, RuleKind, RuleResult, SourceMap,
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
fn use_warning_renders_with_fixed_id_span_and_allow_filter() {
    let source = "function Check(p){return 7;}";
    run_case(source, "Check", |results, sources| {
        let findings: Vec<_> = results
            .findings()
            .iter()
            .filter(|finding| finding.kind() == RuleKind::UnusedParameterValue)
            .cloned()
            .collect();
        assert_eq!(findings.len(), 1);
        let path = std::env::temp_dir()
            .join(format!("circomspect-uses-sarif-{}.json", std::process::id()));
        let rendered =
            support::render(&findings, sources, MessageCategory::Warning, &[], &path).unwrap();
        assert_eq!(rendered, (1, 1));
        let sarif: serde_json::Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        let results = sarif["runs"][0]["results"].as_array().unwrap();
        assert_eq!(results[0]["ruleId"], "CS0007");
        assert_eq!(results[0]["level"], "warning");
        assert_eq!(results[0]["locations"][0]["physicalLocation"]["region"]["startLine"], 1);
        let hidden =
            support::render(&findings, sources, MessageCategory::Warning, &["CS0007"], &path)
                .unwrap();
        assert_eq!(hidden, (0, 0));
    });
}
