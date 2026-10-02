use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::BitDecomposition;
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ProjectSummaries, SummaryFact,
};
use circomspect_program_analysis::new_rules::RuleContext;
use parser::hir::{lift_project, AccessPath, AccessStep, ArrayIndex, HirProject, LiftedProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

const BODY: &str = "signal input in;signal output bits[3];\
    bits[0]<--0;bits[1]<--0;bits[2]<--0;\
    bits[0]*(bits[0]-1)===0;bits[1]*(bits[1]-1)===0;\
    bits[2]*(bits[2]-1)===0;in===bits[0]+2*bits[1]+4*bits[2];";

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-scoped-bits-{}-{:?}",
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

fn path(hir: &HirProject, name: &str, index: Option<usize>) -> AccessPath {
    let symbol = hir.symbols().iter().find(|symbol| symbol.name == name).unwrap();
    let mut steps = Vec::new();
    if let Some(index) = index {
        steps.push(AccessStep::Index {
            index: ArrayIndex::Constant(index.to_string()),
            span: symbol.span,
        });
    }
    AccessPath {
        root: symbol.id,
        terminal: symbol.id,
        steps,
        component_input: false,
        component_output: false,
        span: symbol.span,
    }
}

fn query(extra: &str, budget: Option<usize>) -> SummaryFact<Option<BitDecomposition>> {
    let source = format!("template Bits(){{{BODY}{extra}}}");
    query_source(&source, budget)
}

fn query_source(source: &str, budget: Option<usize>) -> SummaryFact<Option<BitDecomposition>> {
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("Bits").unwrap();
    let evidence = if lifted.hir.mains().is_empty() {
        provider.symbolic_root(definition).unwrap()
    } else {
        let site = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph().reachable_main_call(site.id(), &lifted.hir)
        else {
            panic!("main must be reachable");
        };
        provider.main_evidence(&call).unwrap()
    };
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, budget).unwrap();
    let input = path(&lifted.hir, "in", None);
    let bits = [
        path(&lifted.hir, "bits", Some(0)),
        path(&lifted.hir, "bits", Some(1)),
        path(&lifted.hir, "bits", Some(2)),
    ];
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    context.template_bit_decomposition(&input, &bits)
}

#[test]
fn valid_library_root_exposes_only_a_provider_scoped_relation() {
    for extra in ["", "if(0){assert(0);}"] {
        let result = query(extra, None);
        let certificate = result.certified().unwrap().as_ref().unwrap();
        assert_eq!(certificate.bits().len(), 3);
    }
}

#[test]
fn known_execution_failure_and_incomplete_source_withhold_scoped_relation() {
    for extra in ["assert(0);", "var z=1/0;", "signal s[-1];", "var z=Missing();"] {
        let result = query(extra, None);
        assert!(result.unavailable().is_some(), "{extra}: {result:?}");
    }
}

#[test]
fn custom_template_header_withholds_scoped_relation() {
    let source = format!("pragma custom_templates;template custom Bits(){{{BODY}}}");
    let lifted = fixture(&source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("Bits").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let input = path(&lifted.hir, "in", None);
    let bits = [path(&lifted.hir, "bits", Some(0))];
    let result = provider.template_bit_decomposition(&facts, &evidence, &input, &bits);
    assert!(result.unavailable().is_some(), "{result:?}");
}

#[test]
fn incomplete_solver_cannot_release_a_scoped_relation() {
    let result = query("", Some(0));
    assert!(result.unavailable().is_some(), "{result:?}");
}

#[test]
fn foreign_curve_and_project_cannot_rebind_a_scoped_relation() {
    let source = format!("template Bits(){{{BODY}}}");
    let lifted = fixture(&source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("Bits").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let input = path(&lifted.hir, "in", None);
    let bits = [path(&lifted.hir, "bits", Some(0))];

    let other_curve = ProjectSummaries::build(&lifted, Curve::Goldilocks).unwrap();
    let result = other_curve.template_bit_decomposition(&facts, &evidence, &input, &bits);
    assert!(result.unavailable().is_some(), "{result:?}");

    let foreign = fixture(&source);
    let other_project = ProjectSummaries::build(&foreign, Curve::Bn254).unwrap();
    let result = other_project.template_bit_decomposition(&facts, &evidence, &input, &bits);
    assert!(result.unavailable().is_some(), "{result:?}");
}

#[test]
fn evidence_from_another_definition_cannot_rebind_facts() {
    let source = format!("template Bits(){{{BODY}}}template Other(){{}}");
    let lifted = fixture(&source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("Bits").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let other = provider.symbolic_root(lifted.hir.definition("Other").unwrap()).unwrap();
    let input = path(&lifted.hir, "in", None);
    let bits = [path(&lifted.hir, "bits", Some(0))];
    let result = provider.template_bit_decomposition(&facts, &other, &input, &bits);
    assert!(result.unavailable().is_some(), "{result:?}");
}

#[test]
fn called_scope_abstains_until_incoming_constraints_are_proved() {
    let source = format!(
        "template Bits(){{{BODY}}}template T(){{component c=Bits();c.in<==0;}}component main=T();"
    );
    let lifted = fixture(&source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let main_site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main_call) =
        provider.graph().reachable_main_call(main_site.id(), &lifted.hir)
    else {
        panic!("main must be reachable");
    };
    let main = provider.main_evidence(&main_call).unwrap();
    let main_cfg = build_cfg(&lifted.hir, main.context().definition()).unwrap();
    let main_facts = provider.analyze_for_evidence(&main_cfg, &main, None).unwrap();
    let child_site =
        provider.graph().calls_from(CallOwner::Definition(main.context().definition()))[0];
    let CallReachability::Reachable(child_call) =
        provider.graph().reachable_call(child_site.id(), &main_facts)
    else {
        panic!("child must be reachable");
    };
    let child = provider.call_evidence(&child_call, &main_facts, &main).unwrap();
    let child_cfg = build_cfg(&lifted.hir, child.context().definition()).unwrap();
    let child_facts = provider.analyze_for_evidence(&child_cfg, &child, None).unwrap();
    let input = path(&lifted.hir, "in", None);
    let bits = [
        path(&lifted.hir, "bits", Some(0)),
        path(&lifted.hir, "bits", Some(1)),
        path(&lifted.hir, "bits", Some(2)),
    ];
    let result = provider.template_bit_decomposition(&child_facts, &child, &input, &bits);
    assert!(result.unavailable().is_some(), "{result:?}");
}

#[test]
fn main_and_independent_valid_definitions_retain_their_scoped_relation() {
    for suffix in [
        "component main=Bits();",
        "template Broken(){var z=Missing();}",
        "function Bad(n,n){return 0;}",
    ] {
        let source = format!("template Bits(){{{BODY}}}{suffix}");
        let result = query_source(&source, None);
        assert!(result.certified().and_then(Option::as_ref).is_some(), "{suffix}: {result:?}");
    }
}
