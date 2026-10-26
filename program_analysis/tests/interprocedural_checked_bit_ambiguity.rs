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
use circomspect_program_analysis::hir_facts::{BitAmbiguityOutcome, NoBitAmbiguityCertificate};
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ContextEvidence, ProjectAnalysis, SummaryFact,
};
use circomspect_program_analysis::rules::RuleContext;
use parser::hir::{lift_project, DefinitionRef, HirProject, LiftedProject, PortId};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-checked-bit-models-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let file = directory.join("case.circom");
    fs::write(&file, source).unwrap();
    let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    lifted
}

fn source(width: usize, extra: &str) -> String {
    format!(
        "template Bits(n){{signal input in;signal output out[n];var sum=0;\
         for(var i=0;i<n;i++){{out[i]<--0;out[i]*(out[i]-1)===0;\
         sum+=out[i]*(2**i);}}sum===in;{extra}}}component main=Bits({width});"
    )
}

fn port(hir: &HirProject, name: &str) -> PortId {
    let Some(DefinitionRef::Template(id)) = hir.definition("Bits") else {
        panic!("Bits template must exist")
    };
    for candidate in &hir.template(id).unwrap().ports {
        let item = hir.port(*candidate).unwrap();
        if hir.symbol(item.symbol).is_some_and(|symbol| symbol.name == name) {
            return *candidate;
        }
    }
    panic!("port {name} must exist")
}

fn main_evidence(provider: &ProjectAnalysis<'_>, hir: &HirProject) -> ContextEvidence {
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_main_call(site.id(), hir)
    else {
        panic!("main must be reachable")
    };
    provider.contexts().main_evidence(&call).unwrap()
}

fn inspect(
    source: &str,
    curve: Curve,
    width: usize,
    budget: Option<usize>,
) -> SummaryFact<BitAmbiguityOutcome> {
    let lifted = fixture(source);
    let provider = ProjectAnalysis::build(&lifted, curve).unwrap();
    let evidence = main_evidence(&provider, &lifted.hir);
    let cfg = build_cfg(&lifted.hir, evidence.context().definition()).unwrap();
    let complete = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let input = complete.port_handle(port(&lifted.hir, "in"), &[]).unwrap();
    let mut bits = Vec::with_capacity(width);
    for index in 0..width {
        bits.push(complete.port_handle(port(&lifted.hir, "out"), &[index]).unwrap());
    }
    let facts = if let Some(budget) = budget {
        provider.contexts().analyze_for_evidence(&cfg, &evidence, Some(budget)).unwrap()
    } else {
        complete
    };
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    context.template_bit_ambiguity_handles(&input, &bits)
}

#[test]
fn checked_small_width_has_no_ambiguity_certificate() {
    let result = inspect(&source(3, ""), Curve::Goldilocks, 3, None);
    assert_eq!(
        result.certified(),
        Some(&BitAmbiguityOutcome::NoCertificate(
            NoBitAmbiguityCertificate::WidthBelowFieldModulus
        ))
    );
}

#[test]
fn checked_canonical_goldilocks_loop_proves_two_complete_models() {
    let result = inspect(&source(64, ""), Curve::Goldilocks, 64, None);
    let Some(BitAmbiguityOutcome::Proved(proof)) = result.certified() else {
        panic!("expected a verified pair: {result:?}");
    };
    assert_eq!(proof.decomposition().bits().len(), 64);
    assert_eq!(proof.constraint_origins().len(), 65);
    assert_ne!(proof.representations()[0].bits(), proof.representations()[1].bits());
    assert_eq!(
        proof.assignments()[0].get(proof.decomposition().input()),
        Some(proof.input_value())
    );
    assert_eq!(
        proof.assignments()[1].get(proof.decomposition().input()),
        Some(proof.input_value())
    );
}

#[test]
fn checked_canonical_bn254_loop_preserves_every_bit_and_constraint_origin() {
    let result = inspect(&source(254, ""), Curve::Bn254, 254, None);
    let Some(BitAmbiguityOutcome::Proved(proof)) = result.certified() else {
        panic!("expected a verified BN254 pair: {result:?}");
    };
    assert_eq!(proof.decomposition().bits().len(), 254);
    assert_eq!(proof.constraint_origins().len(), 255);
    assert_ne!(proof.representations()[0].bits(), proof.representations()[1].bits());
    for assignment in proof.assignments() {
        assert_eq!(assignment.get(proof.decomposition().input()), Some(proof.input_value()));
    }
}

#[test]
fn checked_models_keep_other_external_inputs_equal() {
    let result = inspect(&source(64, "signal input other;other===7;"), Curve::Goldilocks, 64, None);
    let Some(BitAmbiguityOutcome::Proved(proof)) = result.certified() else {
        panic!("expected a verified pair: {result:?}");
    };
    let input = proof.decomposition().input();
    let bits = proof.decomposition().bits();
    let external: Vec<_> =
        proof.assignments()[0].keys().filter(|key| *key != input && !bits.contains(key)).collect();
    assert_eq!(external.len(), 1);
    assert_eq!(proof.assignments()[0].get(external[0]), proof.assignments()[1].get(external[0]));
}

#[test]
fn checked_models_respect_extra_constraints_and_missing_relations() {
    let restricted = inspect(&source(64, "out[0]===0;"), Curve::Goldilocks, 64, None);
    assert_eq!(
        restricted.certified(),
        Some(&BitAmbiguityOutcome::NoCertificate(NoBitAmbiguityCertificate::CandidatesRejected))
    );
    let missing = source(64, "").replace("out[i]*(out[i]-1)===0;", "");
    let missing = inspect(&missing, Curve::Goldilocks, 64, None);
    assert_eq!(
        missing.certified(),
        Some(&BitAmbiguityOutcome::NoCertificate(
            NoBitAmbiguityCertificate::NoMatchingDecomposition
        ))
    );
    let witness_only = source(64, "")
        .replace("signal input in;", "signal output in;")
        .replace("sum===in;", "in<--sum;");
    let witness_only = inspect(&witness_only, Curve::Goldilocks, 64, None);
    assert_eq!(
        witness_only.certified(),
        Some(&BitAmbiguityOutcome::NoCertificate(
            NoBitAmbiguityCertificate::NoMatchingDecomposition
        ))
    );
}

#[test]
fn checked_models_withhold_incomplete_analysis() {
    let result = inspect(&source(64, ""), Curve::Goldilocks, 64, Some(0));
    assert!(result.unavailable().is_some(), "{result:?}");
}

#[test]
fn checked_handles_enforce_context_curve_project_and_bounds() {
    let lifted = fixture(&source(3, ""));
    let gold = ProjectAnalysis::build(&lifted, Curve::Goldilocks).unwrap();
    let evidence = main_evidence(&gold, &lifted.hir);
    let cfg = build_cfg(&lifted.hir, evidence.context().definition()).unwrap();
    let facts = gold.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let input_port = port(&lifted.hir, "in");
    let output_port = port(&lifted.hir, "out");
    let input = facts.port_handle(input_port, &[]).unwrap();
    let mut bits = Vec::new();
    for index in 0..3 {
        bits.push(facts.port_handle(output_port, &[index]).unwrap());
    }
    assert!(facts.port_handle(output_port, &[3]).is_err());
    let context = RuleContext::new(&facts, &gold, &evidence).unwrap();
    let bn = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let bn_evidence = main_evidence(&bn, &lifted.hir);
    let bn_facts = bn.contexts().analyze_for_evidence(&cfg, &bn_evidence, None).unwrap();
    let bn_input = bn_facts.port_handle(input_port, &[]).unwrap();
    let different_context =
        gold.contexts().symbolic_root(lifted.hir.definition("Bits").unwrap()).unwrap();
    let symbolic = gold.contexts().analyze_for_evidence(&cfg, &different_context, None).unwrap();
    let symbolic_input = symbolic.port_handle(input_port, &[]).unwrap();
    let foreign = fixture(&source(3, ""));
    let foreign_provider = ProjectAnalysis::build(&foreign, Curve::Goldilocks).unwrap();
    let foreign_evidence = main_evidence(&foreign_provider, &foreign.hir);
    let foreign_cfg = build_cfg(&foreign.hir, foreign_evidence.context().definition()).unwrap();
    let foreign_facts = foreign_provider
        .contexts()
        .analyze_for_evidence(&foreign_cfg, &foreign_evidence, None)
        .unwrap();
    let foreign_input = foreign_facts.port_handle(port(&foreign.hir, "in"), &[]).unwrap();
    for candidate in [&bn_input, &symbolic_input, &foreign_input] {
        let result = context.template_bit_ambiguity_handles(candidate, &bits);
        assert!(result.unavailable().is_some(), "{result:?}");
    }
    let correct = context.template_bit_ambiguity_handles(&input, &bits);
    assert!(correct.certified().is_some(), "{correct:?}");
}

#[test]
fn checked_models_refuse_called_and_symbolic_parameter_scopes() {
    let child_source = source(3, "").replace(
        "component main=Bits(3);",
        "template Parent(){component c=Bits(3);}component main=Parent();",
    );
    let lifted = fixture(&child_source);
    let provider = ProjectAnalysis::build(&lifted, Curve::Goldilocks).unwrap();
    let parent = main_evidence(&provider, &lifted.hir);
    let parent_cfg = build_cfg(&lifted.hir, parent.context().definition()).unwrap();
    let parent_facts =
        provider.contexts().analyze_for_evidence(&parent_cfg, &parent, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent.context().definition()))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_call(site.id(), &parent_facts)
    else {
        panic!("child must be reachable")
    };
    let child = provider.contexts().call_evidence(&call, &parent_facts, &parent).unwrap();
    let child_cfg = build_cfg(&lifted.hir, child.context().definition()).unwrap();
    let child_facts = provider.contexts().analyze_for_evidence(&child_cfg, &child, None).unwrap();
    let input = child_facts.port_handle(port(&lifted.hir, "in"), &[]).unwrap();
    let bit = child_facts.port_handle(port(&lifted.hir, "out"), &[0]).unwrap();
    let context = RuleContext::new(&child_facts, &provider, &child).unwrap();
    let called = context.template_bit_ambiguity_handles(&input, &[bit]);
    assert!(called.unavailable().is_some(), "{called:?}");

    let symbolic = fixture("template Bits(n){signal input in;signal output out[3];}");
    let provider = ProjectAnalysis::build(&symbolic, Curve::Goldilocks).unwrap();
    let definition = symbolic.hir.definition("Bits").unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(&symbolic.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let input = facts.port_handle(port(&symbolic.hir, "in"), &[]).unwrap();
    let bit = facts.port_handle(port(&symbolic.hir, "out"), &[0]).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    let symbolic_result = context.template_bit_ambiguity_handles(&input, &[bit]);
    assert!(symbolic_result.unavailable().is_some(), "{symbolic_result:?}");
}
