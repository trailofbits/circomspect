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

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::Incidence;
use circomspect_program_analysis::interprocedural::{CallOwner, CallReachability, ProjectSummaries};
use parser::hir::{lift_project, AccessPath, LiftedProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-internal-incidence-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let source_path = directory.join("case.circom");
    fs::write(&source_path, source).unwrap();
    let loaded =
        load_sources(&[source_path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty());
    lifted
}

fn internal_incidence(source: &str, budget: Option<usize>) -> Option<Incidence> {
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, budget).unwrap();
    let symbol = lifted.hir.symbols().iter().find(|symbol| symbol.name == "s").unwrap();
    let path = AccessPath {
        root: symbol.id,
        terminal: symbol.id,
        steps: Vec::new(),
        component_input: false,
        component_output: false,
        span: symbol.span,
    };
    provider.template_internal_signal_incidence(&facts, &evidence, &path).certified().copied()
}

#[test]
fn internal_signal_incidence_uses_generated_constraints_only() {
    for (statement, expected) in [
        ("", Incidence::Zero),
        ("s<--1;", Incidence::Zero),
        ("s<==1;", Incidence::Must),
        ("s<--1;s===1;", Incidence::Must),
    ] {
        let source = format!("template T(){{signal s;{statement}}}");
        assert_eq!(internal_incidence(&source, None), Some(expected), "{source}");
    }
}

#[test]
fn invalid_template_execution_cannot_certify_internal_incidence() {
    for statement in ["assert(0);", "var bad[-1];", "var bad=1/0;"] {
        let source = format!("template T(){{{statement}signal s;s<--1;}}");
        assert_eq!(internal_incidence(&source, None), None, "{source}");
    }
    let source = concat!(
        "function F(){assert(0);return 7;}",
        "template T(){var unused=F();signal s;s<--1;}"
    );
    assert_eq!(internal_incidence(source, None), None);
}

#[test]
fn external_custom_exported_and_foreign_signals_are_not_internal_facts() {
    for source in [
        "pragma custom_templates; template custom T(){signal s;s<--1;}",
        "template extern_c T(){signal s;s<--1;}",
        "template T(){signal output s;s<--1;}",
        "template T(){signal input s;}",
        "template T(){var s=1;}",
        "template U(){signal s;s<--1;} template T(){}",
    ] {
        assert_eq!(internal_incidence(source, None), None, "{source}");
    }
}

#[test]
fn internal_incidence_keeps_budget_and_symbolic_alias_blockers() {
    for budget in 0..80 {
        let source = "template T(){signal input c;signal s;if(c){s===1;}}";
        assert_ne!(internal_incidence(source, Some(budget)), Some(Incidence::Zero));
    }
    assert_eq!(internal_incidence("template T(){signal s;s<--1;}", Some(0)), None);
}

#[test]
fn main_and_called_contexts_keep_their_own_scope() {
    let source = concat!(
        "template Child(){signal s;s<--1;}",
        "template T(){signal t;t<--1;component c=Child();} component main=T();"
    );
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(main.id(), provider.hir())
    else {
        panic!("main call must be reachable")
    };
    let root = provider.main_evidence(&main).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &root, None).unwrap();
    let symbol = lifted.hir.symbols().iter().find(|symbol| symbol.name == "t").unwrap();
    let path = AccessPath {
        root: symbol.id,
        terminal: symbol.id,
        steps: Vec::new(),
        component_input: false,
        component_output: false,
        span: symbol.span,
    };
    let result = provider.template_internal_signal_incidence(&facts, &root, &path);
    assert_eq!(result.certified(), Some(&Incidence::Zero));
    let symbolic = provider.symbolic_root(definition).unwrap();
    let mismatched = provider.template_internal_signal_incidence(&facts, &symbolic, &path);
    assert!(mismatched.certified().is_none());

    let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("child call must be reachable")
    };
    let child = provider.call_evidence(&call, &facts, &root).unwrap();
    let cfg = build_cfg(&lifted.hir, child.context().definition()).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &child, None).unwrap();
    let symbol = lifted.hir.symbols().iter().find(|symbol| symbol.name == "s").unwrap();
    let path = AccessPath { root: symbol.id, terminal: symbol.id, span: symbol.span, ..path };
    let result = provider.template_internal_signal_incidence(&facts, &child, &path);
    assert!(result.certified().is_none(), "{result:?}");
}

#[test]
fn internal_arrays_keep_element_context_and_failure_scope() {
    use abstract_interpretation::graph::FlowGraph;
    use circomspect_program_analysis::hir_cfg::CfgNodeKind;
    for (body, expected) in [
        ("signal s[2];s[0]<--1;s[1]<==1;", Some(Incidence::Zero)),
        ("signal s[2];s[0]<--1;s[0]===1;", Some(Incidence::Must)),
        ("signal s[2];var i=0;s[i]<--1;", Some(Incidence::Zero)),
        ("signal s[2];s[2]<--1;", None),
        ("signal s[0];s[0]<--1;", None),
        ("signal input c;signal s[2];var i=0;if(c){i=1;}s[i]<--1;", None),
        ("signal s[2];s[0]<--1;var x=Missing();", None),
    ] {
        let lifted = fixture(&format!("template T(){{{body}}}"));
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("T").unwrap();
        let evidence = provider.symbolic_root(definition).unwrap();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let path = facts
            .cfg()
            .nodes()
            .iter()
            .find_map(|id| {
                let CfgNodeKind::Witness { target, .. } = &facts.cfg().node(*id)?.kind else {
                    return None;
                };
                Some(target)
            })
            .unwrap();
        let fact = provider.template_internal_signal_incidence(&facts, &evidence, path);
        assert_eq!(fact.certified().copied(), expected, "{body}: {fact:?}");
    }
}

#[test]
fn nested_required_failure_blocks_internal_certificates() {
    let source = concat!(
        "function F(n){n=[1,2];var x=n[1];return 7;}",
        "function G(){return F([2]);}",
        "template T(){var x=G();signal s;s<--1;}"
    );
    assert_eq!(internal_incidence(source, None), None);
}
