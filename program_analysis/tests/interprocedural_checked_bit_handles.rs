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
use circomspect_program_analysis::hir_facts::BitDecomposition;
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ContextEvidence, ProjectSummaries, SummaryFact,
};
use circomspect_program_analysis::new_rules::RuleContext;
use parser::hir::{lift_project, DefinitionRef, HirProject, PortId};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn port(hir: &HirProject, name: &str) -> PortId {
    let Some(DefinitionRef::Template(id)) = hir.definition("Bits") else {
        panic!("Bits template must exist")
    };
    for port in &hir.template(id).unwrap().ports {
        let port_data = hir.port(*port).unwrap();
        if hir.symbol(port_data.symbol).is_some_and(|symbol| symbol.name == name) {
            return *port;
        }
    }
    panic!("port {name} must exist")
}

fn main_evidence(provider: &ProjectSummaries<'_>, hir: &HirProject) -> ContextEvidence {
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_main_call(site.id(), hir)
    else {
        panic!("main must be reachable")
    };
    provider.main_evidence(&call).unwrap()
}

fn scoped(extra: &str) -> SummaryFact<Option<BitDecomposition>> {
    let source = format!(
        "template Bits(n){{signal input in;signal output out[n];var sum=0;\
         for(var i=0;i<n;i++){{out[i]<--0;out[i]*(out[i]-1)===0;\
         sum+=out[i]*(2**i);}}{extra}sum===in;}}component main=Bits(3);"
    );
    let directory = std::env::temp_dir().join(format!(
        "circomspect-scoped-handles-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let file = directory.join("case.circom");
    fs::write(&file, source).unwrap();
    let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    let provider = ProjectSummaries::build(&lifted, Curve::Goldilocks).unwrap();
    let evidence = main_evidence(&provider, &lifted.hir);
    let cfg = build_cfg(&lifted.hir, evidence.context().definition()).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let input = facts.port_handle(port(&lifted.hir, "in"), &[]).unwrap();
    let mut bits = Vec::new();
    for index in 0..3 {
        bits.push(facts.port_handle(port(&lifted.hir, "out"), &[index]).unwrap());
    }
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    context.template_bit_decomposition_handles(&input, &bits)
}

#[test]
fn validated_main_exposes_checked_element_relation() {
    let result = scoped("");
    let Some(Some(proof)) = result.certified() else { panic!("{result:?}") };
    assert_eq!(proof.bits().len(), 3);
}

#[test]
fn failed_main_cannot_issue_checked_element_relation() {
    let result = scoped("assert(0);");
    assert!(result.unavailable().is_some(), "{result:?}");
}

#[test]
fn a_checked_handle_from_another_curve_cannot_authorize_the_relation() {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-foreign-bit-handle-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let file = directory.join("case.circom");
    fs::write(
        &file,
        "template Bits(){signal input in;signal output out[1];\
         out[0]<--0;out[0]*(out[0]-1)===0;in===out[0];}component main=Bits();",
    )
    .unwrap();
    let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    let definition = lifted.hir.definition("Bits").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let gold = ProjectSummaries::build(&lifted, Curve::Goldilocks).unwrap();
    let gold_evidence = main_evidence(&gold, &lifted.hir);
    let gold_facts = gold.analyze_for_evidence(&cfg, &gold_evidence, None).unwrap();
    let context = RuleContext::new(&gold_facts, &gold, &gold_evidence).unwrap();
    let bn = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let bn_evidence = main_evidence(&bn, &lifted.hir);
    let bn_facts = bn.analyze_for_evidence(&cfg, &bn_evidence, None).unwrap();
    let input = bn_facts.port_handle(port(&lifted.hir, "in"), &[]).unwrap();
    let bit = bn_facts.port_handle(port(&lifted.hir, "out"), &[0]).unwrap();
    let result = context.template_bit_decomposition_handles(&input, &[bit]);
    assert!(result.unavailable().is_some(), "{result:?}");
}
