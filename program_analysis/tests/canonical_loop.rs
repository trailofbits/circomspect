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
use circomspect_program_analysis::hir_facts::{BitDecomposition, Fact};
use circomspect_program_analysis::interprocedural::{CallOwner, CallReachability, ProjectSummaries};
use parser::hir::{lift_project, AccessStep, ArrayIndex, DefinitionRef, ExprKind, HirProject, PortId};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn port(hir: &HirProject, name: &str) -> PortId {
    let Some(DefinitionRef::Template(id)) = hir.definition("Bits") else {
        panic!("Bits template must exist")
    };
    let template = hir.template(id).unwrap();
    for port in &template.ports {
        let item = hir.port(*port).unwrap();
        if hir.symbol(item.symbol).is_some_and(|symbol| symbol.name == name) {
            return *port;
        }
    }
    panic!("port {name} must exist")
}

fn inspect(count: usize, curve: Curve) -> Fact<Option<BitDecomposition>> {
    inspect_with_extra(count, curve, "")
}

fn inspect_with_extra(count: usize, curve: Curve, extra: &str) -> Fact<Option<BitDecomposition>> {
    let source = format!(
        "template Bits(n){{signal input in;signal output out[n];var sum=0;\
         for(var i=0;i<n;i++){{out[i]<--0;out[i]*(out[i]-1)===0;\
         sum+=out[i]*(2**i);}}{extra}sum===in;}}component main=Bits({count});"
    );
    let directory = std::env::temp_dir().join(format!(
        "circomspect-loop-red-{}-{:?}",
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
    let provider = ProjectSummaries::build(&lifted, curve).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &lifted.hir)
    else {
        panic!("expected reachable main");
    };
    let evidence = provider.main_evidence(&call).unwrap();
    let cfg = build_cfg(&lifted.hir, evidence.context().definition()).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    if count > 1 {
        let out = lifted.hir.port(port(&lifted.hir, "out")).unwrap().symbol;
        let source_index = lifted
            .hir
            .expressions()
            .iter()
            .find_map(|expression| {
                let ExprKind::Access(path) = &expression.kind else { return None };
                if path.root != out {
                    return None;
                }
                let [AccessStep::Index { index: ArrayIndex::Symbolic(_), .. }] =
                    path.steps.as_slice()
                else {
                    return None;
                };
                Some(path)
            })
            .unwrap();
        assert!(facts.exact_access_key(source_index).certified().is_none());
    }
    let input = facts.port_handle(port(&lifted.hir, "in"), &[]).unwrap();
    let mut bits = Vec::new();
    for index in 0..count {
        bits.push(facts.port_handle(port(&lifted.hir, "out"), &[index]).unwrap());
    }
    facts.bit_decomposition_handles(&input, &bits)
}

#[test]
fn specialized_canonical_loop_proves_local_three_bit_relation() {
    let fact = inspect(3, Curve::Goldilocks);
    assert!(fact.certified().is_some_and(Option::is_some), "{fact:?}");
}

#[test]
fn goldilocks_64_bit_canonical_loop_proves_every_element() {
    let fact = inspect(64, Curve::Goldilocks);
    let Some(Some(proof)) = fact.certified() else { panic!("{fact:?}") };
    assert_eq!(proof.bits().len(), 64);
}

#[test]
fn bn254_canonical_loop_proves_every_element() {
    let fact = inspect(254, Curve::Bn254);
    let Some(Some(proof)) = fact.certified() else { panic!("{fact:?}") };
    assert_eq!(proof.bits().len(), 254);
}

#[test]
fn empty_decomposition_cannot_claim_a_bit_relation() {
    let fact = inspect(0, Curve::Goldilocks);
    assert!(fact.certified().and_then(Option::as_ref).is_none());
}

#[test]
fn an_unrelated_out_of_bounds_write_cannot_validate_the_body() {
    let fact = inspect_with_extra(3, Curve::Goldilocks, "out[n]<--0;");
    assert!(fact.certified().is_none(), "{fact:?}");
}

#[test]
fn symbolic_library_root_cannot_name_a_parameter_sized_bit() {
    let directory =
        std::env::temp_dir().join(format!("circomspect-symbolic-bits-{}", std::process::id()));
    fs::create_dir_all(&directory).unwrap();
    let file = directory.join("case.circom");
    fs::write(
        &file,
        "template Bits(n){signal input in;signal output out[n];\
         for(var i=0;i<n;i++){out[i]<--0;out[i]*(out[i]-1)===0;}}",
    )
    .unwrap();
    let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    let definition = lifted.hir.definition("Bits").unwrap();
    let provider = ProjectSummaries::build(&lifted, Curve::Goldilocks).unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    assert!(facts.port_handle(port(&lifted.hir, "out"), &[0]).is_err());
}
