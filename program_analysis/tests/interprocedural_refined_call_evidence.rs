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
use circomspect_program_analysis::hir_facts::FactBlocker;
use circomspect_program_analysis::interprocedural::{
    AnalyzeEvidenceError, ArgumentValue, CallBlocker, CallOwner, CallProvenance, CallReachability,
    ContextOrigin, ProjectSummaries, SummaryBlocker,
};
use circomspect_program_analysis::new_rules::{run_registered, RuleContext, RuleKind};
use parser::hir::{lift_project, IncompleteReason, LiftedProject, SemanticCode};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-refined-call-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

#[test]
fn exact_provisional_function_call_carries_main_ancestry_to_numeric_rule() {
    let source = concat!(
        "function F(){return ",
        "21888242871839275222246405745257275088548364400416034343698204186575808495617;}",
        "template T(){var x=F();}component main=T();"
    );
    let lifted = fixture(source);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    let provider = ProjectSummaries::build(&lifted, Curve::Bls12_381).unwrap();
    let parent = lifted.hir.definition("T").unwrap();
    let child = lifted.hir.definition("F").unwrap();
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(main.id(), &lifted.hir)
    else {
        panic!("main T() must be reachable")
    };
    let parent_evidence = provider.main_evidence(&main).unwrap();
    let parent_cfg = build_cfg(&lifted.hir, parent).unwrap();
    let parent_facts = provider.analyze_for_evidence(&parent_cfg, &parent_evidence, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Unavailable(CallBlocker::ProvisionalSite) =
        provider.graph().reachable_call(site.id(), &parent_facts)
    else {
        panic!("raw graph must keep a provisional call unavailable")
    };
    let child_evidence = provider
        .refined_function_call_evidence(site.id(), &parent_facts, &parent_evidence)
        .unwrap();
    assert_eq!(child_evidence.origin(), ContextOrigin::Call(site.id()));
    assert_eq!(child_evidence.context().definition(), child);
    assert!(provider.check_evidence(&child_evidence).is_ok());
    let child_cfg = build_cfg(&lifted.hir, child).unwrap();
    let child_facts = provider.analyze_for_evidence(&child_cfg, &child_evidence, None).unwrap();
    let context = RuleContext::new(&child_facts, &provider, &child_evidence).unwrap();
    assert_eq!(context.call_path().len(), 2);
    assert_eq!(context.call_path()[0].owner(), CallOwner::Main(0));
    assert_eq!(context.call_path()[1].owner(), CallOwner::Definition(parent));
    let results = run_registered(&context).unwrap();
    assert!(results
        .findings()
        .iter()
        .any(|finding| finding.kind() == RuleKind::Bn254SpecificCircuit));
}

#[test]
fn exact_function_call_in_a_library_retains_symbolic_parent_ancestry() {
    let lifted = fixture("function F(){return 7;} template T(){var x=F();}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("T").unwrap();
    let caller = provider.symbolic_root(parent).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    assert_eq!(site.provenance, CallProvenance::Provisional);
    let child = provider.refined_function_call_evidence(site.id(), &facts, &caller).unwrap();
    assert_eq!(child.origin(), ContextOrigin::Call(site.id()));
    let cfg = build_cfg(&lifted.hir, lifted.hir.definition("F").unwrap()).unwrap();
    let child_facts = provider.analyze_for_evidence(&cfg, &child, None).unwrap();
    let rule_context = RuleContext::new(&child_facts, &provider, &child).unwrap();
    assert_eq!(rule_context.call_path().len(), 1);
    assert_eq!(rule_context.call_path()[0].owner(), CallOwner::Definition(parent));
}

fn refined_call_after(source: &str) -> Result<(), SummaryBlocker> {
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("T").unwrap();
    let caller = provider.symbolic_root(parent).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    provider.refined_function_call_evidence(site.id(), &facts, &caller).map(|_| ())
}

#[test]
fn known_caller_failure_cannot_mint_refined_child_evidence() {
    for source in [
        "function F(){return 7;}template T(){assert(0);var x=F();}",
        "function F(){return 7;}template T(){var z=1/0;var x=F();}",
        "function F(){return 7;}template T(){if(1){assert(0);}var x=F();}",
        "function F(){return 7;}function T(){assert(0);var x=F();return x;}",
    ] {
        assert_eq!(refined_call_after(source), Err(SummaryBlocker::UnsupportedContext));
    }
    assert_eq!(
        refined_call_after("function F(){return 7;}template T(){assert(1);var x=F();}"),
        Ok(())
    );
    assert_eq!(
        refined_call_after("function F(){return 7;}template T(){if(0){assert(0);}var x=F();}"),
        Ok(())
    );
}

#[test]
fn warning_scope_rejects_custom_templates_before_rules_run() {
    let lifted = fixture("pragma custom_templates;template custom T(){signal s;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    assert_eq!(context.check_warning_execution_scope(), Err(SummaryBlocker::ExternalSummary));
}

#[test]
fn symbolic_scalar_parameter_does_not_fail_warning_scope_validation() {
    let lifted = fixture("template T(n){var x=~n;}");
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    assert!(
        lifted.incomplete.iter().all(|region| region.reason == IncompleteReason::UnknownType),
        "{:?}",
        lifted.incomplete
    );
    let provider = ProjectSummaries::build(&lifted, Curve::Goldilocks).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    assert_eq!(context.check_warning_execution_scope(), Ok(()));
}

fn warning_scope_result(source: &str) -> Result<(), SummaryBlocker> {
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    context.check_warning_execution_scope()
}

#[test]
fn warning_scope_keeps_missing_callee_and_source_errors_blocked() {
    for source in [
        "template T(){var x=Missing();}",
        "template T(){var x=;var y=1;}",
        "template T(){var x=1;var x=2;}",
    ] {
        assert_eq!(warning_scope_result(source), Err(SummaryBlocker::IncompleteDefinition));
    }
}

fn ordinary_call_after(source: &str) -> Result<(), SummaryBlocker> {
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("T").unwrap();
    let caller = provider.symbolic_root(parent).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("component call must remain may-reachable in the raw graph")
    };
    provider.call_evidence(&call, &facts, &caller).map(|_| ())
}

#[test]
fn known_caller_failure_cannot_mint_ordinary_child_evidence() {
    for source in [
        "template C(){var p=7;}template T(){assert(0);component c=C();}",
        "template C(){var p=7;}template T(){var z=1/0;component c=C();}",
    ] {
        assert_eq!(ordinary_call_after(source), Err(SummaryBlocker::UnsupportedContext));
    }
    assert_eq!(
        ordinary_call_after("template C(){var p=7;}template T(){assert(1);component c=C();}"),
        Ok(())
    );
}

#[test]
fn foreign_site_or_caller_cannot_authorize_a_refined_call() {
    let lifted = fixture("function F(){return 7;} template T(){var x=F();}component main=T();");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("T").unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(site.id(), &lifted.hir)
    else {
        panic!("main T() must be reachable")
    };
    let caller = provider.main_evidence(&main).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let wrong_caller = provider.symbolic_root(lifted.hir.definition("F").unwrap()).unwrap();
    assert_eq!(
        provider.refined_function_call_evidence(site.id(), &facts, &wrong_caller),
        Err(SummaryBlocker::WrongContext)
    );
    let foreign = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let foreign_site = foreign.graph().calls_from(CallOwner::Definition(parent))[0];
    assert_eq!(
        provider.refined_function_call_evidence(foreign_site.id(), &facts, &caller),
        Err(SummaryBlocker::ForeignCall)
    );
    let wrong_curve = ProjectSummaries::build(&lifted, Curve::Bls12_381).unwrap();
    assert_eq!(
        wrong_curve.refined_function_call_evidence(site.id(), &facts, &caller),
        Err(SummaryBlocker::WrongContext)
    );
}

#[test]
fn dead_provisional_call_never_becomes_a_reachable_child_scope() {
    let source =
        concat!("function F(){return 7;} template T(){if(0){var x=F();}}", "component main=T();");
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("T").unwrap();
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(main.id(), &lifted.hir)
    else {
        panic!("main T() must be reachable")
    };
    let caller = provider.main_evidence(&main).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    assert_eq!(
        provider.refined_function_call_evidence(site.id(), &facts, &caller),
        Err(SummaryBlocker::ExternalSummary)
    );
}

#[test]
fn unknown_argument_and_budgeted_facts_cannot_mint_a_child_scope() {
    let lifted = fixture("function F(n){return n;} template T(p){var x=F(p);}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("T").unwrap();
    let caller = provider.symbolic_root(parent).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    assert_eq!(
        provider.refined_function_call_evidence(site.id(), &facts, &caller),
        Err(SummaryBlocker::ExternalSummary)
    );

    let lifted = fixture("function F(){return 7;} template T(){var x=F();}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("T").unwrap();
    let caller = provider.symbolic_root(parent).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, Some(0)).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let result = provider.refined_function_call_evidence(site.id(), &facts, &caller);
    let Err(SummaryBlocker::LocalFacts(blockers)) = result else {
        panic!("budgeted facts must retain their typed blocker: {result:?}")
    };
    assert!(blockers.iter().any(|blocker| {
        let FactBlocker::Budget(_) = blocker else { return false };
        true
    }));
}

#[test]
fn preserved_index_call_requires_checked_reachability_instead_of_refinement() {
    let lifted = fixture(concat!(
        "function F(n){return n;} ",
        "template T(){signal output y[2];y[F(0)]<==1;}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("T").unwrap();
    let caller = provider.symbolic_root(parent).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    assert_eq!(site.provenance, CallProvenance::EffectOwned);
    assert_eq!(
        provider.refined_function_call_evidence(site.id(), &facts, &caller),
        Err(SummaryBlocker::ForeignCall)
    );
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("the preserved index call must be reachable")
    };
    let evidence = provider.call_evidence(&call, &facts, &caller).unwrap();
    assert_eq!(evidence.context().definition(), lifted.hir.definition("F").unwrap());
    assert_eq!(evidence.origin(), ContextOrigin::Call(site.id()));
    let [ArgumentValue::Scalar(value)] = evidence.context().arguments() else {
        panic!("the index call must retain its scalar argument")
    };
    assert_eq!(*value.as_bigint(), 0.into());
}

#[test]
fn unattached_anonymous_input_call_cannot_mint_refined_evidence() {
    let lifted = fixture(concat!(
        "function F(){return 1;}",
        "template Child(){signal input in;signal output out;out<==in;}",
        "template T(){signal output y;y<==Child()(in<==F());}"
    ));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("T").unwrap();
    let caller = provider.symbolic_root(parent).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider
        .graph()
        .calls_from(CallOwner::Definition(parent))
        .into_iter()
        .find(|site| site.resolved() == lifted.hir.definition("F"))
        .unwrap();
    assert_eq!(site.provenance, CallProvenance::Unattached);
    assert_eq!(
        provider.refined_function_call_evidence(site.id(), &facts, &caller),
        Err(SummaryBlocker::ForeignCall)
    );
}

#[test]
fn invalid_array_target_cannot_mint_evidence() {
    let lifted = fixture("function F(){return 7;} template T(){var x[2];x=F();}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("T").unwrap();
    let caller = provider.symbolic_root(parent).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let error = provider.analyze_for_evidence(&cfg, &caller, None).err().unwrap();
    match error {
        AnalyzeEvidenceError::Blocked(SummaryBlocker::InvalidAssignment(_))
        | AnalyzeEvidenceError::InvalidAssignment { .. } => {}
        AnalyzeEvidenceError::Blocked(blocker) => panic!("wrong blocker: {blocker:?}"),
        AnalyzeEvidenceError::InvalidValueUse { diagnostic, .. } => {
            assert_eq!(diagnostic.code, SemanticCode::InvalidAssignment);
        }
    }
}

#[test]
fn unresolved_function_name_cannot_be_authorized_by_a_provisional_site() {
    let lifted = fixture("template T(){var x=Missing();}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("T").unwrap();
    let caller = provider.symbolic_root(parent).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    assert_eq!(site.provenance, CallProvenance::Provisional);
    assert_eq!(
        provider.refined_function_call_evidence(site.id(), &facts, &caller),
        Err(SummaryBlocker::ExternalSummary)
    );
}

#[test]
fn independent_argument_kinds_and_nested_calls_keep_exact_ancestry() {
    for source in [
        "function F(n){return n+1;}template T(){var x=F(2);}",
        "function F(n){return 7;}template T(){var x=F([1,2]);}",
        "function G(){return 2;}function F(n){return n+1;}template T(){var x=F(G());}",
    ] {
        let lifted = fixture(source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let parent = lifted.hir.definition("T").unwrap();
        let caller = provider.symbolic_root(parent).unwrap();
        let cfg = build_cfg(&lifted.hir, parent).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
        let mut accepted = 0;
        for site in provider.graph().calls_from(CallOwner::Definition(parent)) {
            if site.provenance == CallProvenance::Provisional {
                let evidence = provider
                    .refined_function_call_evidence(site.id(), &facts, &caller)
                    .unwrap_or_else(|error| panic!("{source}: {error:?}"));
                assert_eq!(evidence.context().definition(), site.resolved().unwrap());
                provider.check_evidence(&evidence).unwrap();
                accepted += 1;
            }
        }
        assert!(accepted > 0, "{source}");
    }
}

#[test]
fn independent_budget_matrix_never_certifies_multivalued_or_unknown_arguments() {
    for source in [
        "function F(n){return n;}template T(){var n=0;while(n<2){var x=F(n);n++;}}",
        "function F(n){return 7;}template T(){signal input n;var x=F(n);}",
        "function F(n){return 7;}template T(p){var x=F([1,p]);}",
    ] {
        let lifted = fixture(source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let parent = lifted.hir.definition("T").unwrap();
        let caller = provider.symbolic_root(parent).unwrap();
        let cfg = build_cfg(&lifted.hir, parent).unwrap();
        for budget in (0..64).map(Some).chain([None]) {
            let facts = provider.analyze_for_evidence(&cfg, &caller, budget).unwrap();
            for site in provider.graph().calls_from(CallOwner::Definition(parent)) {
                assert!(
                    provider.refined_function_call_evidence(site.id(), &facts, &caller).is_err(),
                    "{source}, budget {budget:?}"
                );
            }
        }
    }
}

#[test]
fn independent_same_definition_different_scope_and_project_are_rejected() {
    let source = "function F(){return 7;}template T(){var x=F();}component main=T();";
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("T").unwrap();
    let root = provider.symbolic_root(parent).unwrap();
    let main_site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(main_site.id(), &lifted.hir)
    else {
        panic!("main")
    };
    let main = provider.main_evidence(&main).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &main, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    assert_eq!(
        provider.refined_function_call_evidence(site.id(), &facts, &root),
        Err(SummaryBlocker::WrongContext)
    );
    let foreign_lifted = fixture(source);
    let foreign = ProjectSummaries::build(&foreign_lifted, Curve::Bn254).unwrap();
    assert!(foreign.refined_function_call_evidence(site.id(), &facts, &main).is_err());
}

#[test]
fn independent_required_failure_before_call_cannot_certify_reachable_child() {
    for prefix in ["assert(0);", "var z=1/0;"] {
        let source = format!("function F(){{return 7;}}template T(){{{prefix}var x=F();}}");
        let lifted = fixture(&source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let parent = lifted.hir.definition("T").unwrap();
        let caller = provider.symbolic_root(parent).unwrap();
        let cfg = build_cfg(&lifted.hir, parent).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
        assert!(
            provider.refined_function_call_evidence(site.id(), &facts, &caller).is_err(),
            "must not certify a call after {prefix}"
        );
    }
}

#[test]
fn independent_impossible_child_calls_do_not_emit_numeric_warnings() {
    let mut observed = Vec::new();
    for prefix in ["assert(0);", "var z=1/0;"] {
        let source = format!(
            concat!(
                "function F(){{return ",
                "21888242871839275222246405745257275088548364400416034343698204186575808495617;}}",
                "template T(){{{prefix}var x=F();}}"
            ),
            prefix = prefix
        );
        let lifted = fixture(&source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bls12_381).unwrap();
        let parent = lifted.hir.definition("T").unwrap();
        let caller = provider.symbolic_root(parent).unwrap();
        let cfg = build_cfg(&lifted.hir, parent).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
        let count = match provider.refined_function_call_evidence(site.id(), &facts, &caller) {
            Err(_) => 0,
            Ok(child) => {
                let cfg = build_cfg(&lifted.hir, child.context().definition()).unwrap();
                let facts = provider.analyze_for_evidence(&cfg, &child, None).unwrap();
                let context = RuleContext::new(&facts, &provider, &child).unwrap();
                run_registered(&context)
                    .unwrap()
                    .findings()
                    .iter()
                    .filter(|finding| finding.kind() == RuleKind::Bn254SpecificCircuit)
                    .count()
            }
        };
        observed.push((prefix, count));
    }
    assert_eq!(observed, vec![("assert(0);", 0), ("var z=1/0;", 0)]);
}

#[test]
fn independent_function_caller_required_failure_cannot_certify_a_child() {
    let mut accepted = Vec::new();
    for prefix in ["assert(0);", "var z=1/0;"] {
        let source =
            format!("function F(){{return 7;}}function T(){{{prefix}var x=F();return x;}}");
        let lifted = fixture(&source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let parent = lifted.hir.definition("T").unwrap();
        let caller = provider.symbolic_root(parent).unwrap();
        let cfg = build_cfg(&lifted.hir, parent).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
        accepted.push(provider.refined_function_call_evidence(site.id(), &facts, &caller).is_ok());
    }
    assert_eq!(accepted, vec![false, false]);
}

#[test]
fn independent_ordinary_calls_cannot_authorize_warnings_after_known_failure() {
    let mut emitted = Vec::new();
    for prefix in ["assert(0);", "var z=1/0;"] {
        let source = format!(
            concat!(
                "template Child(){{var x=",
                "21888242871839275222246405745257275088548364400416034343698204186575808495617;}}",
                "template T(){{{prefix}component c=Child();}}"
            ),
            prefix = prefix
        );
        let lifted = fixture(&source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bls12_381).unwrap();
        let parent = lifted.hir.definition("T").unwrap();
        let caller = provider.symbolic_root(parent).unwrap();
        let cfg = build_cfg(&lifted.hir, parent).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
        let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
        else {
            panic!("raw graph call is reachable before refusal");
        };
        let count = match provider.call_evidence(&call, &facts, &caller) {
            Err(_) => 0,
            Ok(child) => {
                let cfg = build_cfg(&lifted.hir, child.context().definition()).unwrap();
                let facts = provider.analyze_for_evidence(&cfg, &child, None).unwrap();
                let context = RuleContext::new(&facts, &provider, &child).unwrap();
                run_registered(&context)
                    .unwrap()
                    .findings()
                    .iter()
                    .filter(|finding| finding.kind() == RuleKind::Bn254SpecificCircuit)
                    .count()
            }
        };
        emitted.push(count);
    }
    assert_eq!(emitted, vec![0, 0]);
}

#[test]
fn independent_scope_refusal_keeps_dead_and_unknown_failures_distinct() {
    for (source, accepted) in [
        ("template T(){assert(1);var x=1;}", true),
        ("template T(){if(0){assert(0);}var x=1;}", true),
        ("template T(){signal input p;assert(p);var x=1;}", true),
        ("function Broken(){var x=Missing();return 7;}template T(){var x=1;}", true),
        ("function T(){if(0){assert(0);}return 7;}", true),
        ("template T(){signal input p;if(p){assert(0);}var x=1;}", false),
        ("template T(){var x=1;assert(0);}", false),
        ("pragma custom_templates;template custom T(){var x=1;}", false),
        ("template extern_c T(){var x=1;}", false),
        ("template T(){var x=Missing();}", false),
    ] {
        let lifted = fixture(source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let parent = lifted.hir.definition("T").unwrap();
        let caller = provider.symbolic_root(parent).unwrap();
        let cfg = build_cfg(&lifted.hir, parent).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
        assert_eq!(
            provider.check_warning_execution_scope(&facts, &caller).is_ok(),
            accepted,
            "{source}"
        );
    }
}

#[test]
fn independent_partial_callers_keep_exact_calls_but_block_scope_warnings() {
    for source in [
        "function F(){return 7;}template T(){var x=F();var z=Missing();}",
        "template F(){signal output x;x<==7;}template T(){component c=F();var z=Missing();}",
    ] {
        let lifted = fixture(source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("T").unwrap();
        let caller = provider.symbolic_root(definition).unwrap();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
        let child = match provider.graph().reachable_call(site.id(), &facts) {
            CallReachability::Reachable(call) => provider.call_evidence(&call, &facts, &caller),
            CallReachability::Unavailable(CallBlocker::ProvisionalSite) => {
                provider.refined_function_call_evidence(site.id(), &facts, &caller)
            }
            CallReachability::Unreachable => panic!("unexpected dead call: {source}"),
            CallReachability::Unavailable(blocker) => panic!("{source}: {blocker:?}"),
        };
        assert!(child.is_ok(), "{source}: {child:?}");
        assert_eq!(
            provider.check_warning_execution_scope(&facts, &caller),
            Err(SummaryBlocker::IncompleteDefinition)
        );
    }
}

#[test]
fn independent_warning_refusal_prioritizes_binding_then_failure_over_partial_source() {
    let source =
        "function F(){return 7;}template T(){assert(0);var x=F();var z=Missing();}template U(){}";
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let caller = provider.symbolic_root(definition).unwrap();
    let other = provider.symbolic_root(lifted.hir.definition("U").unwrap()).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
    assert_eq!(
        provider.check_warning_execution_scope(&facts, &other),
        Err(SummaryBlocker::WrongContext)
    );
    assert_eq!(
        provider.check_warning_execution_scope(&facts, &caller),
        Err(SummaryBlocker::UnsupportedContext)
    );
    let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
    assert!(provider.refined_function_call_evidence(site.id(), &facts, &caller).is_err());
}
