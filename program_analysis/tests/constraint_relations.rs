use std::fs;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use circomspect_program_analysis::hir_cfg::{build_cfg, CfgNodeKind, DefinitionCfg};
use circomspect_program_analysis::hir_facts::{AnalysisFacts, Fact, FactBlocker, GeneratedEquation};
use circomspect_program_analysis::interprocedural::{ContextOrigin, ProjectSummaries};
use parser::hir::lift_project;
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn witness(cfg: &DefinitionCfg) -> NodeId {
    for id in cfg.nodes() {
        let Some(node) = cfg.node(*id) else { continue };
        if let CfgNodeKind::Witness { .. } = node.kind {
            return *id;
        }
    }
    panic!("witness site")
}

fn inspect_with_budget(
    source: &str,
    curve: Curve,
    budget: Option<usize>,
) -> Fact<Option<GeneratedEquation>> {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-relations-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    let definition = lifted.hir.definition("T").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let provider = ProjectSummaries::build(&lifted, curve).unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let facts: AnalysisFacts<'_> = provider.analyze_for_evidence(&cfg, &evidence, budget).unwrap();
    facts.must_equation_for_witness(witness(&cfg))
}

fn inspect(source: &str, curve: Curve) -> Fact<Option<GeneratedEquation>> {
    inspect_with_budget(source, curve, None)
}

#[test]
fn quadratic_equations_combine_terms_and_order_factors() {
    let source = "template T(){signal input a;signal input b;signal output x;\
                  x<--a*b+a*b;x===2*b*a;}";
    let fact = inspect(source, Curve::Bn254);
    let certificate = fact.certified().unwrap().as_ref().unwrap();
    assert_eq!(certificate.constraint_origins().len(), 1);
    assert_eq!(certificate.context().origin(), ContextOrigin::SymbolicRoot);
    let witness = certificate.witness_origin().span;
    let constraint = certificate.constraint_origins()[0].span;
    assert_eq!(&source[witness.start()..witness.end()], "x<--a*b+a*b");
    assert_eq!(&source[constraint.start()..constraint.end()], "x===2*b*a;");
}

#[test]
fn nonzero_field_scaling_preserves_the_same_equation() {
    let source = "template T(){signal input a;signal output x;x<--a;x*2===a*2;}";
    let fact = inspect(source, Curve::Bn254);
    assert!(fact.certified().unwrap().is_some());
}

#[test]
fn subtraction_and_unary_negation_keep_operand_order() {
    let same = "template T(){signal input a;signal input b;signal output x;x<--a-b;x===a+(-b);}";
    let fact = inspect(same, Curve::Bn254);
    assert!(fact.certified().unwrap().is_some(), "{fact:?}");

    let different = "template T(){signal input a;signal input b;signal output x;x<--a-b;x===b-a;}";
    let fact = inspect(different, Curve::Bn254);
    assert!(fact.certified().unwrap().is_none(), "{fact:?}");
}

#[test]
fn left_associated_254_term_linear_relation_has_no_recursion_limit() {
    let mut sum = String::from("a");
    for _ in 0..253 {
        sum.push_str("+1");
    }
    let source = format!("template T(){{signal input a;signal output x;x<--{sum};x==={sum};}}");
    let fact = inspect(&source, Curve::Bn254);
    assert!(fact.certified().is_some_and(Option::is_some), "{fact:?}");
}

#[test]
fn witness_write_alone_never_certifies_an_equation() {
    let source = "template T(){signal input a;signal input b;signal output x;x<--a*b;}";
    let fact = inspect(source, Curve::Bn254);
    assert!(fact.certified().unwrap().is_none());
}

#[test]
fn unreachable_witness_write_cannot_borrow_a_generated_equation() {
    let source = "template T(){signal input a;signal output x;if(0){x<--a;}x===a;}";
    let fact = inspect(source, Curve::Bn254);
    assert!(fact.certified().unwrap().is_none());
}

#[test]
fn out_of_bounds_witness_and_generated_constraint_cannot_certify_equivalence() {
    let witness = "template T(){signal input a;signal output x[1];x[1]<--a;x[1]===a;}";
    let fact = inspect(witness, Curve::Bn254);
    assert!(fact.unavailable().unwrap().contains(&FactBlocker::AggregateAccess));

    let constraint = "template T(){signal input a;signal output x[1];x[0]<--a;x[1]===a;}";
    let fact = inspect(constraint, Curve::Bn254);
    assert!(fact.unavailable().unwrap().contains(&FactBlocker::AggregateAccess));

    let extra_constraint =
        "template T(){signal input a;signal output x[1];x[0]<--a;x[0]===a;x[1]===a;}";
    let fact = inspect(extra_constraint, Curve::Bn254);
    assert!(fact.unavailable().unwrap().contains(&FactBlocker::AggregateAccess));
}

#[test]
fn in_bounds_indexed_signal_retains_a_generated_equation_certificate() {
    let source = "template T(){signal input a;signal output x[1];x[0]<--a;x[0]===a;}";
    let fact = inspect(source, Curve::Bn254);
    assert!(fact.certified().unwrap().is_some());
}

#[test]
fn different_equation_does_not_certify_redundancy() {
    let source = "template T(){signal input a;signal input b;signal output x;\
                  x<--a*b;x===a+b;}";
    let fact = inspect(source, Curve::Bn254);
    assert!(fact.certified().unwrap().is_none());
}

#[test]
fn repeated_witness_then_generated_assignment_cannot_certify_equivalence() {
    let source = "template T(){signal input a;signal input b;signal output x;\
                  x<--a*b;x<==b*a;}";
    let fact = inspect(source, Curve::Bn254);
    assert!(fact.certified().and_then(Option::as_ref).is_none());
}

#[test]
fn incomplete_solver_cannot_release_a_provisional_equation() {
    let source = "template T(){signal input a;signal output x;x<--a;x===a;}";
    let fact = inspect_with_budget(source, Curve::Bn254, Some(0));
    let blockers = fact.unavailable().expect("budget must block certification");
    assert!(blockers.iter().any(|blocker| match blocker {
        FactBlocker::Budget(_) => true,
        FactBlocker::OpaqueNode(_, _)
        | FactBlocker::OpaqueEdge(_, _)
        | FactBlocker::ExternalSummary
        | FactBlocker::AggregateAccess
        | FactBlocker::DeferredShape(_)
        | FactBlocker::AggregateConstraint(_)
        | FactBlocker::DeferredControl(_)
        | FactBlocker::OpaqueExpression(_)
        | FactBlocker::UnsupportedRelation(_)
        | FactBlocker::WitnessWrite(_, _)
        | FactBlocker::SignalRead(_, _)
        | FactBlocker::MissingExit
        | FactBlocker::ForeignQuery
        | FactBlocker::ForeignDefinition => false,
    }));
}

#[test]
fn field_bound_polynomials_do_not_cross_curves() {
    let source = "template T(){signal input a;signal output x;x<--a+1;x===a+1;}";
    let bn = inspect(source, Curve::Bn254);
    let bls = inspect(source, Curve::Bls12_381);
    let bn = bn.certified().unwrap().as_ref().unwrap();
    let bls = bls.certified().unwrap().as_ref().unwrap();
    assert_ne!(bn.equation(), bls.equation());
}

#[test]
fn unsupported_constraint_blocks_a_negative_equation_claim() {
    let source = "template T(){signal input a;signal output x;x<--a;x===a*a*a;}";
    let fact = inspect(source, Curve::Bn254);
    let blockers = fact.unavailable().expect("unsupported equation must remain unknown");
    assert!(blockers.iter().any(|blocker| match blocker {
        FactBlocker::UnsupportedRelation(_) => true,
        FactBlocker::Budget(_)
        | FactBlocker::OpaqueNode(_, _)
        | FactBlocker::OpaqueEdge(_, _)
        | FactBlocker::ExternalSummary
        | FactBlocker::AggregateAccess
        | FactBlocker::DeferredShape(_)
        | FactBlocker::AggregateConstraint(_)
        | FactBlocker::DeferredControl(_)
        | FactBlocker::OpaqueExpression(_)
        | FactBlocker::WitnessWrite(_, _)
        | FactBlocker::SignalRead(_, _)
        | FactBlocker::MissingExit
        | FactBlocker::ForeignQuery
        | FactBlocker::ForeignDefinition => false,
    }));
}

#[test]
fn querying_independent_writes_in_either_order_keeps_the_same_certificates() {
    let source = "template T(){signal input a;signal input b;signal output x;signal output y;\
                  x<--a;y<--b;x===a;y===b;}";
    let directory = std::env::temp_dir().join(format!(
        "circomspect-relations-order-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    let definition = lifted.hir.definition("T").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let witnesses: Vec<_> = cfg
        .nodes()
        .iter()
        .filter_map(|id| {
            let node = cfg.node(*id)?;
            let CfgNodeKind::Witness { .. } = node.kind else { return None };
            Some(*id)
        })
        .collect();
    assert_eq!(witnesses.len(), 2);
    let first = facts.must_equation_for_witness(witnesses[0]);
    let second = facts.must_equation_for_witness(witnesses[1]);
    assert!(first.certified().unwrap().is_some());
    assert!(second.certified().unwrap().is_some());
    let reverse_facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let second_first = reverse_facts.must_equation_for_witness(witnesses[1]);
    let first_second = reverse_facts.must_equation_for_witness(witnesses[0]);
    assert_eq!(first, first_second);
    assert_eq!(second, second_first);
}

#[test]
fn witness_constant_does_not_replace_signal_in_equation() {
    let source = "template T(){signal input a;signal output x;x<--7;x===a;}";
    let fact = inspect(source, Curve::Bn254);
    assert!(fact.certified().unwrap().is_none(), "{fact:?}");
}

#[test]
fn local_scalar_value_at_each_site_is_preserved() {
    let source = "template T(){signal input a;signal output x;var v=1;x<--v*a;v=2;x===v*a;}";
    let fact = inspect(source, Curve::Bn254);
    assert!(fact.certified().unwrap().is_none(), "{fact:?}");
}

#[test]
fn signal_guarded_equations_do_not_certify_generated_constraints() {
    let source = "template T(){signal input a;signal input c;signal output x;\
                  x<--a;if(c){x===a;}else{x===a;}}";
    let fact = inspect(source, Curve::Bn254);
    assert!(fact.unavailable().is_some(), "{fact:?}");
}
