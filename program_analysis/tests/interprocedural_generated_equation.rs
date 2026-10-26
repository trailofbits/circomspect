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
use std::fs;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use circomspect_program_analysis::hir_cfg::{CfgNodeKind, DefinitionCfg};
use circomspect_program_analysis::hir_facts::GeneratedEquation;
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ContextOrigin, ProjectAnalysis, SummaryBlocker, SummaryFact,
};
use parser::hir::{lift_project, HirProject, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn first_witness(cfg: &DefinitionCfg) -> NodeId {
    for id in cfg.nodes() {
        let Some(node) = cfg.node(*id) else { continue };
        if let CfgNodeKind::Witness { .. } = &node.kind {
            return *id;
        }
    }
    panic!("expected a witness write");
}

fn witness_for(cfg: &DefinitionCfg, hir: &HirProject, name: &str) -> NodeId {
    for id in cfg.nodes() {
        let Some(node) = cfg.node(*id) else { continue };
        let CfgNodeKind::Witness { target, .. } = &node.kind else { continue };
        if hir.symbol(target.root).is_some_and(|symbol| symbol.name == name) {
            return *id;
        }
    }
    panic!("expected a witness write to {name}");
}

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-equation-provider-{}-{:?}",
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

#[test]
fn provider_certifies_generated_equation_in_valid_template_scope() {
    let source = "template T(){signal input a;signal output x;x<--a;x===a;}";
    let lifted = fixture(source);
    let definition = lifted.hir.definition("T").unwrap();
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = circomspect_program_analysis::hir_cfg::build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let result = provider
        .template_generated_equations(&facts, &evidence)
        .for_witness(first_witness(facts.cfg()));
    let certificate = result.certified().unwrap().as_ref().unwrap();
    assert_eq!(certificate.context(), &evidence);
    assert_eq!(certificate.context().origin(), ContextOrigin::SymbolicRoot);
    assert_eq!(certificate.constraint_origins().len(), 1);
}

#[test]
fn provider_rejects_a_foreign_evidence_context() {
    let source = "template T(){signal input a;signal output x;x<--a;x===a;}\
                  template U(){signal input b;signal output y;y<--b;y===b;}";
    let lifted = fixture(source);
    let definition = lifted.hir.definition("T").unwrap();
    let other = lifted.hir.definition("U").unwrap();
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let foreign = provider.contexts().symbolic_root(other).unwrap();
    let cfg = circomspect_program_analysis::hir_cfg::build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let result =
        provider.template_generated_equations(&facts, &foreign).for_witness(first_witness(&cfg));
    assert!(result.unavailable().unwrap().contains(&SummaryBlocker::WrongContext));
}

fn nested_equation(constraint_rhs: &str) -> SummaryFact<Option<GeneratedEquation>> {
    let source = format!(
        "function F(){{return 1;}}function G(){{return F();}}\
         template T(){{signal output x;x<--G();x==={constraint_rhs};}}component main=T();"
    );
    let lifted = fixture(&source);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &lifted.hir)
    else {
        panic!("main template must be reachable");
    };
    let evidence = provider.contexts().main_evidence(&call).unwrap();
    let cfg = circomspect_program_analysis::hir_cfg::build_cfg(
        &lifted.hir,
        evidence.context().definition(),
    )
    .unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    provider.template_generated_equations(&facts, &evidence).for_witness(witness_for(
        facts.cfg(),
        &lifted.hir,
        "x",
    ))
}

fn symbolic_equation(source: &str) -> SummaryFact<Option<GeneratedEquation>> {
    let lifted = fixture(source);
    let definition = lifted.hir.definition("T").unwrap();
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = circomspect_program_analysis::hir_cfg::build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    provider.template_generated_equations(&facts, &evidence).for_witness(witness_for(
        facts.cfg(),
        &lifted.hir,
        "x",
    ))
}

#[test]
fn nested_exact_function_results_normalize_in_a_main_template() {
    let result = nested_equation("1");
    let certificate = result.certified().unwrap_or_else(|| {
        panic!("complete exact nested return: {:?}", result.unavailable());
    });
    assert!(certificate.is_some(), "nested call RHS equals generated constraint");
}

#[test]
fn exact_function_result_in_generated_constraint_matches_nested_witness_call() {
    let result = nested_equation("F()");
    let certificate = result.certified().unwrap_or_else(|| {
        panic!("both call results have exact evidence: {:?}", result.unavailable());
    });
    assert!(certificate.is_some(), "exact call results normalize on both sides");
}

#[test]
fn exact_call_result_does_not_match_a_different_generated_value() {
    let result = nested_equation("2");
    let certificate = result.certified().expect("different exact equations remain decidable");
    assert!(certificate.is_none());
}

#[test]
fn symbolic_function_result_cannot_validate_opaque_equality() {
    let source = "function F(n){return n;}template T(n){signal output x;x<--1;x===F(n);}";
    let result = symbolic_equation(source);
    assert!(
        result.unavailable().unwrap().contains(&SummaryBlocker::IncompleteDefinition),
        "unknown result must abstain: {result:?}"
    );
}

#[test]
fn failing_function_result_cannot_validate_opaque_equality() {
    let source = "function F(){assert(0);return 1;}template T(){signal output x;x<--1;x===F();}";
    let result = symbolic_equation(source);
    assert!(
        result.unavailable().unwrap().contains(&SummaryBlocker::UnsupportedContext),
        "failing callee must abstain: {result:?}"
    );
}

#[test]
fn generated_equation_before_signal_initialization_cannot_certify() {
    let result = symbolic_equation("template T(){signal output x;x===1;x<--1;}");
    assert!(result.unavailable().is_some(), "read before write must abstain: {result:?}");
}

#[test]
fn generated_equation_after_signal_initialization_can_certify() {
    let result = symbolic_equation("template T(){signal output x;x<--1;x===1;}");
    assert!(result.certified().and_then(Option::as_ref).is_some(), "{result:?}");
}

#[test]
fn witness_rhs_read_before_initialization_cannot_certify() {
    let result = symbolic_equation("template T(){signal a;signal output x;x<--a;a<--1;x===a;}");
    assert!(result.unavailable().is_some(), "witness RHS read must abstain: {result:?}");
}

#[test]
fn self_read_and_branch_only_initialization_cannot_certify() {
    for source in [
        "template T(){signal output x;x<--x+1;x===1;}",
        "template T(n){signal a;signal output x;if(n){a<--1;}x<--a;x===a;}",
    ] {
        let result = symbolic_equation(source);
        assert!(result.unavailable().is_some(), "unready signal read: {result:?}");
    }
}

#[test]
fn exact_signal_readiness_covers_branches_arrays_and_unrelated_constraints() {
    for source in [
        "template T(){signal y;signal output x;if(0){y<--1;}x<--y;x===y;}",
        "template T(n){signal y;signal output x;if(n){y<--1;}x<--y;x===y;}",
        "template T(){signal y[2];signal output x;y[0]<--1;x<--y[1];y[1]<--1;x===y[1];}",
        "template T(){signal output x[2];x[0]<--x[1];x[1]<--1;x[0]===x[1];}",
        "template T(){signal s;signal output x;x<--1;x===1;s===0;s<--0;}",
        "template T(){signal s;var y=s;signal output x;x<--1;x===1;s<--0;}",
        "template T(){signal s;log(s);signal output x;x<--1;x===1;s<--0;}",
    ] {
        let result = symbolic_equation(source);
        assert!(result.unavailable().is_some(), "invalid read must abstain: {source}: {result:?}");
    }
}

#[test]
fn initialized_signal_reads_preserve_generated_equation_proofs() {
    for source in [
        "template T(){signal input a;signal output x;x<--a;x===a;}",
        "template T(){signal y;signal output x;y<--1;x<--y;x===y;}",
        "template T(){signal y;signal output x;if(1){y<--1;}x<--y;x===y;}",
        "template T(){signal y[2];signal output x;y[0]<--1;y[1]<--2;x<--y[1];x===y[1];}",
        "template T(){signal output x;x<--1;x===1;}",
        "template T(){signal input a;signal output x;x<==a;}",
    ] {
        let result = symbolic_equation(source);
        assert!(result.certified().and_then(Option::as_ref).is_some(), "{source}: {result:?}");
    }
}

#[test]
fn generated_constraint_requires_one_source_quadratic_product() {
    for expression in ["a*b+c*d", "a*b+a*c"] {
        let source = format!(
            "template T(){{signal input a;signal input b;signal input c;signal input d;\
             signal output x;x<--{expression};x==={expression};}}"
        );
        let result = symbolic_equation(&source);
        assert!(result.unavailable().is_some(), "invalid generated shape: {result:?}");
    }
}

#[test]
fn source_shape_cannot_use_polynomial_cancellation_as_degree_evidence() {
    for (witness, constraint) in
        [("1", "(a*b)*(c-c)+1"), ("1", "(a-a)*b*c+1"), ("1", "a*b*0*c+1"), ("b*c", "((a-a)+1)*b*c")]
    {
        let source = format!(
            "template T(){{signal input a;signal input b;signal input c;\
             signal output x;x<--{witness};x==={constraint};}}"
        );
        let result = symbolic_equation(&source);
        assert!(result.unavailable().is_some(), "invalid source form: {result:?}");
    }
}

#[test]
fn factored_generated_constraint_matches_witness_polynomial() {
    for source in [
        "template T(){signal input a;signal input b;signal input c;\
         signal output x;x<--a*b+c;x===a*b+c;}",
        "template T(){signal input a;signal input b;signal input c;signal input d;\
         signal output x;x<--(a+b)*(c+d);x===(a+b)*(c+d);}",
        "template T(){signal input a;signal input b;signal output x;\
         x<--a*b+a*b;x===2*b*a;}",
    ] {
        let result = symbolic_equation(source);
        assert!(result.certified().and_then(Option::as_ref).is_some(), "{result:?}");
    }
}

#[test]
fn invalid_unrelated_constraints_block_a_matching_equation() {
    for extra in ["a*b+c*d===1;", "a*b*c===1;"] {
        let source = format!(
            "template T(){{signal input a;signal input b;signal input c;signal input d;\
             signal output x;x<--1;x===1;{extra}}}"
        );
        let result = symbolic_equation(&source);
        assert!(result.unavailable().is_some(), "invalid additional constraint: {result:?}");
    }
}

#[test]
fn input_port_reassignment_cannot_certify_a_generated_equation() {
    for source in [
        "template T(){signal input x;x<--1;x===1;}",
        "template T(){signal input x[2];x[0]<--1;x[0]===1;}",
    ] {
        let result = symbolic_equation(source);
        assert!(result.unavailable().is_some(), "input reassignment must abstain: {result:?}");
    }
}

#[test]
fn input_port_reads_require_exact_indices_and_bounds() {
    let symbolic = "template T(){signal input a[1];signal input i;var y=a[i];\
                    signal output x;x<--1;x===1;}";
    let result = symbolic_equation(symbolic);
    assert!(result.unavailable().is_some(), "unproved input index must abstain: {result:?}");

    let out_of_bounds = "template T(){signal input a[1];var y=a[1];\
                         signal output x;x<--1;x===1;}";
    let result = symbolic_equation(out_of_bounds);
    assert!(result.unavailable().is_some(), "out-of-bounds input read: {result:?}");

    let exact = "template T(){signal input a[1];var y=a[0];\
                 signal output x;x<--1;x===1;}";
    let result = symbolic_equation(exact);
    assert!(result.certified().and_then(Option::as_ref).is_some(), "{result:?}");
}

#[test]
fn provider_refuses_a_template_with_repeated_body_writes() {
    let lifted = fixture("template T(){signal output x;x<--1;x<--2;x===1;}");
    let definition = lifted.hir.definition("T").unwrap();
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = circomspect_program_analysis::hir_cfg::build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let result = provider
        .template_generated_equations(&facts, &evidence)
        .for_witness(first_witness(facts.cfg()));
    assert!(result.unavailable().unwrap().contains(&SummaryBlocker::UnsupportedContext));
}

#[test]
fn incomplete_solver_cannot_release_a_provider_equation() {
    let lifted = fixture("template T(){signal output x;x<--1;x===1;}");
    let definition = lifted.hir.definition("T").unwrap();
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = circomspect_program_analysis::hir_cfg::build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, Some(0)).unwrap();
    let result = provider
        .template_generated_equations(&facts, &evidence)
        .for_witness(first_witness(facts.cfg()));
    let unavailable = result.unavailable().expect("budget must block the provider certificate");
    assert!(unavailable.iter().any(|reason| {
        let SummaryBlocker::LocalFacts(blockers) = reason else { return false };
        blockers.iter().any(|blocker| {
            let circomspect_program_analysis::hir_facts::FactBlocker::Budget(_) = blocker else {
                return false;
            };
            true
        })
    }));
}

#[test]
fn provider_refuses_called_context_until_incoming_constraints_are_known() {
    let source = "template Child(){signal output x;x<--1;x===1;}\
                  template T(){component c=Child();}component main=T();";
    let lifted = fixture(source);
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let root_site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(root_call) =
        provider.graph().reachable_main_call(root_site.id(), &lifted.hir)
    else {
        panic!("main template must be reachable");
    };
    let root = provider.contexts().main_evidence(&root_call).unwrap();
    let root_cfg =
        circomspect_program_analysis::hir_cfg::build_cfg(&lifted.hir, root.context().definition())
            .unwrap();
    let root_facts = provider.contexts().analyze_for_evidence(&root_cfg, &root, None).unwrap();
    let child_site =
        provider.graph().calls_from(CallOwner::Definition(root.context().definition()))[0];
    let CallReachability::Reachable(child_call) =
        provider.graph().reachable_call(child_site.id(), &root_facts)
    else {
        panic!("child template must be reachable");
    };
    let child = provider.contexts().call_evidence(&child_call, &root_facts, &root).unwrap();
    let child_cfg =
        circomspect_program_analysis::hir_cfg::build_cfg(&lifted.hir, child.context().definition())
            .unwrap();
    let child_facts = provider.contexts().analyze_for_evidence(&child_cfg, &child, None).unwrap();
    let result = provider
        .template_generated_equations(&child_facts, &child)
        .for_witness(first_witness(child_facts.cfg()));
    assert!(result.unavailable().unwrap().contains(&SummaryBlocker::ExternalSummary));
}

fn independent_equation(
    source: &str,
    budget: Option<usize>,
) -> Option<circomspect_program_analysis::hir_facts::GeneratedEquation> {
    let lifted = fixture(source);
    let definition = lifted.hir.definition("T").unwrap();
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = circomspect_program_analysis::hir_cfg::build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, budget).ok()?;
    let query = facts.cfg().nodes().iter().copied().find(|id| {
        let Some(node) = facts.cfg().node(*id) else { return false };
        let CfgNodeKind::Witness { target, .. } = &node.kind else { return false };
        facts.hir().symbol(target.root).is_some_and(|symbol| symbol.name == "x")
    })?;
    let result = provider.template_generated_equations(&facts, &evidence).for_witness(query);
    result.certified().cloned().flatten()
}

#[test]
fn independent_equations_keep_source_origins_and_constraint_provenance() {
    for source in [
        "template T(){signal input a;signal input b;signal output x;x<--a*b+a*b;x===2*b*a;}",
        "template T(){signal input a;signal output x[1];x[0]<--a;x[0x0]===a;}",
        "function F(){return 1;}function G(){return F();\
            }template T(){signal output x;x<--G();x===F();}",
        "template T(){signal output x;x<--0;\
            x===21888242871839275222246405745257275088548364400416034343698204186575808495617;}",
    ] {
        let proof = independent_equation(source, None).unwrap_or_else(|| panic!("{source}"));
        let witness = proof.witness_origin().span;
        assert!(source[witness.start()..witness.end()].contains("<--"));
        assert!(!proof.constraint_origins().is_empty());
        for origin in proof.constraint_origins() {
            assert!(source[origin.span.start()..origin.span.end()].contains("==="));
        }
    }
    for source in [
        "template T(){signal output x;x<--1;}",
        "template T(){signal output a;signal output x;a<--1;x<--a;x===1;}",
        "template T(){signal output x;x<--0;x===1;}",
        "template T(){signal input a;signal output x[2];x[0]<--a;x[1]===a;}",
        "function F(){return 1;}template T(){signal output x;x<--F();x===2;}",
    ] {
        assert!(independent_equation(source, None).is_none(), "{source}");
    }
}

#[test]
fn independent_equation_scope_rejects_invalid_or_opaque_execution() {
    for source in [
        "template T(){assert(0);signal output x;x<--1;x===1;}",
        "template T(){var z=1/0;signal output x;x<--1;x===1;}",
        "function F(){assert(0);return 1;}template T(){signal output x;x<--F();x===1;}",
        "template T(){signal output x;x<--1;x===1;var z=Missing();}",
        "pragma custom_templates;template custom T(){signal output x;x<--1;x===1;}",
        "template extern_c T(){signal output x;x<--1;x===1;}",
        "template T(){signal output x[0];x[0]<--1;x[0]===1;}",
        "template T(){signal input a;signal output x;x<--a*a*a;x===a*a*a;}",
        "template T(n){signal output x;if(n){x<--1;}x===1;}",
        "function F(n){return 1;}template T(){signal input a;signal output x;x<--1;x===F(a);}",
        "function F(){assert(0);return 1;}template T(){signal output x;x<--1;x===F();}",
        "function F(){return [1];}template T(){signal output x;x<--1;x===F();}",
        "template T(){signal output x;x<--1;x===Missing();}",
        "function F(){return 1;}template T(){signal output x[1];x[0]<--1;x[1]===F();}",
        "function F(){return 1;}template T(){signal output x[1];x[0]<--1;x===F();}",
        "function F(){return 1;}template T(){signal input i;signal output x[2];\
            x[0]<--1;x[i]===F();}",
    ] {
        assert!(independent_equation(source, None).is_none(), "{source}");
    }
    for prefix in ["assert(1);", "var z=1/1;", "if(0){assert(0);}"] {
        let source = format!("template T(){{{prefix}signal output x;x<--1;x===1;}}");
        assert!(independent_equation(&source, None).is_some(), "{source}");
    }
}

#[test]
fn independent_equation_budget_matrix_never_promotes_unknown_nested_calls() {
    for source in [
        "function F(n){return n;}template T(n){signal output x;x<--F(n);x===1;}",
        "function F(n){return 1;}template T(){signal input n;signal output x;x<--F(n);x===1;}",
        "function F(){assert(0);return 1;}template T(){signal output x;x<--F();x===1;}",
    ] {
        for budget in (0..64).map(Some).chain([None]) {
            assert!(independent_equation(source, budget).is_none(), "{source}, {budget:?}");
        }
    }
    let source = "function F(){return 1;}function G(){return F();\
            }template T(){signal output x;x<--G();x===1;}";
    assert!(independent_equation(source, Some(0)).is_none());
    assert!(independent_equation(source, None).is_some());
}

#[test]
fn independent_equation_certificates_reject_provider_curve_and_evidence_mismatch() {
    let source = "template T(){signal output x;x<--1;x===1;}component main=T();";
    let lifted = fixture(source);
    let definition = lifted.hir.definition("T").unwrap();
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let root = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = circomspect_program_analysis::hir_cfg::build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &root, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &lifted.hir)
    else {
        panic!("main")
    };
    let main = provider.contexts().main_evidence(&call).unwrap();
    let query = first_witness(facts.cfg());
    assert!(provider
        .template_generated_equations(&facts, &main)
        .for_witness(query)
        .certified()
        .is_none());
    let other_curve = ProjectAnalysis::build(&lifted, Curve::Bls12_381).unwrap();
    assert!(other_curve
        .template_generated_equations(&facts, &root)
        .for_witness(query)
        .certified()
        .is_none());
    let other_lifted = fixture(source);
    let other = ProjectAnalysis::build(&other_lifted, Curve::Bn254).unwrap();
    assert!(other
        .template_generated_equations(&facts, &root)
        .for_witness(query)
        .certified()
        .is_none());
    assert!(provider
        .template_generated_equations(&facts, &root)
        .for_witness(facts.cfg().entry())
        .certified()
        .is_none());
}

#[test]
fn independent_unsupported_call_equation_forms_remain_precision_gaps() {
    // These valid equalities remain false negatives outside the direct-RHS-call subset.
    for source in [
        "function F(){return 1;}template T(){signal output x;x<--1;F()===x;}",
        "function F(){return 1;}template T(){signal output x;x<--1;x===2*F()-1;}",
    ] {
        assert!(independent_equation(source, None).is_none(), "{source}");
    }
}

#[test]
fn independent_equation_before_witness_initialization_cannot_certify_redundancy() {
    let source = "template T(){signal output x;x===1;x<--1;}";
    assert!(independent_equation(source, None).is_none());
}

#[test]
fn independent_witness_reads_require_prior_initialization_of_the_exact_element() {
    let mut unsound = Vec::new();
    for source in [
        "template T(){signal y;signal output x;x<--y;y<--1;x===y;}",
        "template T(){signal y;signal output x;if(0){y<--1;}x<--y;x===y;}",
        "template T(n){signal y;signal output x;if(n){y<--1;}x<--y;x===y;}",
        "template T(){signal y[2];signal output x;y[0]<--1;x<--y[1];y[1]<--1;x===y[1];}",
        "template T(){signal output x;x<--x;x===x;}",
        "template T(){signal output x[2];x[0]<--x[1];x[1]<--1;x[0]===x[1];}",
        "template T(){signal s;signal output x;x<--1;x===1;s===0;s<--0;}",
    ] {
        if independent_equation(source, None).is_some() {
            unsound.push(source);
        }
    }
    assert!(unsound.is_empty(), "{unsound:#?}");
}

#[test]
fn independent_initialized_input_and_current_write_controls_keep_equations() {
    for source in [
        "template T(){signal input a;signal output x;x<--a;x===a;}",
        "template T(){signal y;signal output x;y<--1;x<--y;x===y;}",
        "template T(){signal y;signal output x;if(1){y<--1;}x<--y;x===y;}",
        "template T(){signal y[2];signal output x;y[0]<--1;y[1]<--2;x<--y[1];x===y[1];}",
        "template T(){signal output x;x<--1;x===1;}",
        "template T(){signal input a;signal output x;x<==a;}",
    ] {
        assert!(independent_equation(source, None).is_some(), "{source}");
    }
}

#[test]
fn independent_initialization_budget_matrix_withholds_invalid_certificates() {
    let mut unsound = Vec::new();
    for source in [
        "template T(){signal output x;x===1;x<--1;}",
        "template T(){signal y;signal output x;x<--y;y<--1;x===y;}",
        "template T(){signal y[2];signal output x;y[0]<--1;x<--y[1];y[1]<--1;x===y[1];}",
    ] {
        for budget in (0..64).map(Some).chain([None]) {
            if independent_equation(source, budget).is_some() {
                unsound.push((source, budget));
            }
        }
    }
    assert!(unsound.is_empty(), "{unsound:#?}");
}

#[test]
fn independent_equation_scope_rejects_nonrelation_uninitialized_signal_reads() {
    for source in [
        "template T(){signal s;var y=s;signal output x;x<--1;x===1;s<--0;}",
        "template T(){signal s;log(s);signal output x;x<--1;x===1;s<--0;}",
    ] {
        assert!(independent_equation(source, None).is_none(), "{source}");
    }
}

#[test]
fn independent_generated_constraint_requires_circom_quadratic_shape() {
    let mut unsound = Vec::new();
    for body in ["x<--a*b+c*d;x===a*b+c*d;", "x<--a*b+a*c;x===a*b+a*c;"] {
        let source = format!(
            "template T(){{signal input a;signal input b;\
            signal input c;signal input d;signal output x;{body}}}"
        );
        if independent_equation(&source, None).is_some() {
            unsound.push(source);
        }
    }
    assert!(unsound.is_empty(), "{unsound:#?}");
}

#[test]
fn independent_generated_constraint_factored_controls_remain_available() {
    for body in ["x<--(a+b)*(c+d);x===(a+b)*(c+d);", "x<--a*b+a*b;x===2*b*a;"] {
        let source = format!(
            "template T(){{signal input a;signal input b;\
            signal input c;signal input d;signal output x;{body}}}"
        );
        assert!(independent_equation(&source, None).is_some(), "{source}");
    }
}

#[test]
fn independent_invalid_additional_constraints_block_an_otherwise_matching_equation() {
    let mut unsound = Vec::new();
    for extra in ["a*b+c*d===1;", "a*b*c===1;"] {
        let source = format!(
            "template T(){{signal input a;signal input b;\
            signal input c;signal input d;signal output x;x<--1;x===1;{extra}}}"
        );
        if independent_equation(&source, None).is_some() {
            unsound.push(source);
        }
    }
    assert!(unsound.is_empty(), "{unsound:#?}");
}

#[test]
fn independent_input_port_write_cannot_certify_an_equation() {
    for source in [
        "template T(){signal input x;x<--1;x===1;}",
        "template T(){signal input x[1];x[0]<--1;x[0]===1;}",
    ] {
        assert!(independent_equation(source, None).is_none(), "{source}");
    }
}

#[test]
fn independent_unproved_input_index_cannot_validate_an_unrelated_equation() {
    for source in [
        "template T(n){signal input a[1];var y=a[n];signal output x;x<--1;x===1;}",
        "template T(){signal input a[1];signal input i;var y=a[i];signal output x;x<--1;x===1;}",
    ] {
        assert!(independent_equation(source, None).is_none(), "{source}");
    }
}

#[test]
fn independent_input_index_bounds_and_proved_controls() {
    for index in ["1", "1+0", "-1"] {
        let source = format!(
            "template T(){{signal input a[1];var y=a[{index}];signal output x;x<--1;x===1;}}"
        );
        assert!(independent_equation(&source, None).is_none(), "{source}");
    }
    for body in ["var y=a[0];", "var y=a[0x0];", "var i=0;var y=a[i];"] {
        let source =
            format!("template T(){{signal input a[1];{body}signal output x;x<--1;x===1;}}");
        assert!(independent_equation(&source, None).is_some(), "{source}");
    }
}

#[test]
fn independent_source_shape_cannot_use_polynomial_cancellation_as_degree_evidence() {
    let mut unsound = Vec::new();
    for rhs in ["(a*b)*(c-c)", "(a-a)*b*c", "a*b*0*c", "((a-a)+1)*b*c"] {
        let source = format!(
            "template T(){{signal input a;signal input b;\
            signal input c;signal output x;x<--{rhs};x==={rhs};}}"
        );
        if independent_equation(&source, None).is_some() {
            unsound.push(source);
        }
    }
    assert!(unsound.is_empty(), "{unsound:#?}");
}

#[test]
fn equation_batch_keeps_each_witness_and_solver_scope_separate() {
    let lifted = fixture(
        "template T(){signal input a;signal output x;signal output y;\
         x<--a;x===a;y<--a+1;y===a+2;}",
    );
    let definition = lifted.hir.definition("T").unwrap();
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = circomspect_program_analysis::hir_cfg::build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let batch = provider.template_generated_equations(&facts, &evidence);
    let x = witness_for(facts.cfg(), &lifted.hir, "x");
    let y = witness_for(facts.cfg(), &lifted.hir, "y");
    assert!(batch.for_witness(x).certified().unwrap().is_some());
    assert!(batch.for_witness(y).certified().unwrap().is_none());
    assert!(batch.for_witness(cfg.entry()).certified().is_none());
    assert!(batch.for_witness(x).certified().unwrap().is_some());
    let incomplete = provider.contexts().analyze_for_evidence(&cfg, &evidence, Some(0)).unwrap();
    let blocked = provider.template_generated_equations(&incomplete, &evidence);
    assert!(blocked.for_witness(x).certified().is_none());
    assert!(blocked.for_witness(y).certified().is_none());
}
