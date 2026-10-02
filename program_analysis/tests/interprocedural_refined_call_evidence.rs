use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::FactBlocker;
use circomspect_program_analysis::interprocedural::{
    AnalyzeEvidenceError, CallBlocker, CallOwner, CallProvenance, CallReachability, ContextOrigin,
    ProjectSummaries, SummaryBlocker,
};
use circomspect_program_analysis::new_rules::{run_registered, RuleContext, RuleKind};
use parser::hir::{lift_project, LiftedProject, SemanticCode};
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
fn unattached_call_and_invalid_array_target_cannot_mint_evidence() {
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
    assert_eq!(site.provenance, CallProvenance::Unattached);
    assert_eq!(
        provider.refined_function_call_evidence(site.id(), &facts, &caller),
        Err(SummaryBlocker::ForeignCall)
    );

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
            assert_eq!(diagnostic.code, SemanticCode::InvalidAssignment)
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
