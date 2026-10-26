// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use abstract_interpretation::graph::FlowGraph;
use circomspect_program_analysis::hir_cfg::{Constraint, build_cfg, CfgNodeKind};
use circomspect_program_analysis::interprocedural::{
    AnalyzeEvidenceError, CallOwner, CallReachability, ProjectAnalysis, SummaryBlocker,
};
use parser::hir::{lift_project, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;
use std::fs;

fn source(argument: &str) -> String {
    format!(
        "template Child(m){{signal input value;signal output bits[m];}}\
         template Compare(n){{signal input operands[2];signal output answer;\
         component d=Child(n+1);d.value<==operands[0]+(1<<n)-operands[1];\
         answer<==1-d.bits[n];}}component main=Compare({argument});"
    )
}

fn lift(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-comparator-shape-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

fn specialized_nodes(source: &str) -> Option<Vec<CfgNodeKind>> {
    let lifted = lift(source);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(main.id(), &lifted.hir)
    else {
        return None;
    };
    let evidence = provider.contexts().main_evidence(&call).ok()?;
    let definition = lifted.hir.definition("Compare").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).ok()?;
    Some(facts.cfg().nodes().iter().map(|id| facts.cfg().node(*id).unwrap().kind.clone()).collect())
}

#[test]
fn exact_scalar_parameter_preserves_both_comparator_constraints() {
    let nodes = specialized_nodes(&source("8")).expect("exact scalar call context");
    let mut targets = Vec::new();
    for node in &nodes {
        if let CfgNodeKind::Constraint(Constraint::Assignment { target: path, .. }) = node {
            targets.push(path.steps.len());
        }
    }
    assert_eq!(targets, [1, 0]);
    for node in &nodes {
        if let CfgNodeKind::OpaqueAssignment { .. } | CfgNodeKind::Opaque(_) = node {
            panic!("exact scalar shape must not leave an opaque assignment: {node:?}");
        }
    }
}

#[test]
fn array_parameter_cannot_specialize_scalar_comparator_assignments() {
    let nodes = specialized_nodes(&source("[8]"));
    if let Some(nodes) = nodes {
        for node in nodes {
            if let CfgNodeKind::Constraint(Constraint::Assignment { .. }) = node {
                panic!("array parameter cannot authorize a scalar constraint");
            }
        }
    }
}

#[test]
fn an_unseeded_library_body_keeps_deferred_assignments_opaque() {
    let source = source("8").replace("component main=Compare(8);", "");
    let lifted = lift(&source);
    let definition = lifted.hir.definition("Compare").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let mut opaque = 0;
    let mut constraints = 0;
    for id in cfg.nodes() {
        let Some(node) = cfg.node(*id) else { continue };
        match &node.kind {
            CfgNodeKind::OpaqueAssignment { .. } => opaque += 1,
            CfgNodeKind::Constraint(Constraint::Assignment { .. }) => constraints += 1,
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::Evaluate(_)
            | CfgNodeKind::LoopHeader
            | CfgNodeKind::Branch { .. }
            | CfgNodeKind::Witness { .. }
            | CfgNodeKind::Constraint(Constraint::Equality { .. })
            | CfgNodeKind::Assignment { .. }
            | CfgNodeKind::DeferredAssignment { .. }
            | CfgNodeKind::Update { .. }
            | CfgNodeKind::Instantiate { .. }
            | CfgNodeKind::OpaqueEquality { .. }
            | CfgNodeKind::Declaration { .. }
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Assert { .. }
            | CfgNodeKind::DeferredAssert { .. }
            | CfgNodeKind::Log
            | CfgNodeKind::Opaque(_) => {}
        }
    }
    assert_eq!((opaque, constraints), (2, 0));
}

#[test]
fn a_written_parameter_cannot_reuse_its_incoming_scalar_seed() {
    let source = source("8").replace("component d=Child(n+1);", "n=9;component d=Child(n+1);");
    let nodes = specialized_nodes(&source).expect("valid mutable parameter context");
    for node in nodes {
        if let CfgNodeKind::Constraint(Constraint::Assignment { .. }) = node {
            panic!("the incoming value of n is stale after a body write");
        }
    }
}

#[test]
fn bus_valued_child_output_cannot_become_a_scalar_answer_constraint() {
    let source = format!(
        "bus B(){{signal x;}}{}",
        source("8").replace("signal output bits[m];", "B output bits[m];")
    );
    let lifted = lift(&source);
    let definition = lifted.hir.definition("Compare").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    for id in cfg.nodes() {
        let Some(node) = cfg.node(*id) else { continue };
        let CfgNodeKind::Constraint(Constraint::Assignment { target: path, .. }) = &node.kind
        else {
            continue;
        };
        assert_ne!(lifted.hir.symbol(path.terminal).unwrap().name, "answer");
    }
}

fn checked_child_bit_zero(argument: &str) -> bool {
    let lifted = lift(&source(argument));
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(main.id(), &lifted.hir)
    else {
        panic!("main call must be reachable")
    };
    let evidence = provider.contexts().main_evidence(&main).unwrap();
    let definition = lifted.hir.definition("Compare").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let child = provider.graph().calls_from(CallOwner::Definition(definition))[0];
    let CallReachability::Reachable(child) = provider.graph().reachable_call(child.id(), &facts)
    else {
        panic!("child call must be reachable")
    };
    let bits =
        lifted.hir.templates().iter().find(|template| template.name == "Child").unwrap().ports[1];
    let applied = provider.apply_component_first_output(&facts, &evidence, &child, bits);
    applied.certified().is_some()
}

#[test]
fn child_port_binding_checks_the_parameterized_dimension() {
    assert!(checked_child_bit_zero("8"));
    assert!(!checked_child_bit_zero("-1"));
}

#[test]
fn exact_scalar_seed_cannot_cross_provider_curve_or_project_identity() {
    let first = lift(&source("8"));
    let second = lift(&source("8"));
    let bn = ProjectAnalysis::build(&first, Curve::Bn254).unwrap();
    let gold = ProjectAnalysis::build(&first, Curve::Goldilocks).unwrap();
    let foreign = ProjectAnalysis::build(&second, Curve::Bn254).unwrap();
    let main = bn.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) = bn.graph().reachable_main_call(main.id(), &first.hir)
    else {
        panic!("main call must be reachable")
    };
    let evidence = bn.contexts().main_evidence(&main).unwrap();
    let cfg = build_cfg(&first.hir, first.hir.definition("Compare").unwrap()).unwrap();
    for provider in [&gold, &foreign] {
        let result = provider.contexts().analyze_for_evidence(&cfg, &evidence, None);
        let Err(AnalyzeEvidenceError::Blocked(SummaryBlocker::WrongContext)) = result else {
            panic!("foreign scalar seed must not specialize a comparator")
        };
    }
}
