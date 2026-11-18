// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::format_push_string,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::Incidence;
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, PortSummary, ProjectAnalysis, SummaryBlocker, SummaryFact,
};
use parser::hir::{lift_project, LiftedProject, PortId};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-incidence-scope-{}-{:?}",
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

fn port(lifted: &LiftedProject, name: &str) -> PortId {
    lifted
        .hir
        .ports()
        .iter()
        .find(|port| lifted.hir.symbol(port.symbol).unwrap().name == name)
        .unwrap()
        .id
}

fn scoped_port(source: &str, budget: Option<usize>, indices: &[usize]) -> SummaryFact<PortSummary> {
    let lifted = fixture(source);
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, budget).unwrap();
    provider.templates().template_port_for_evidence(&facts, &evidence, port(&lifted, "x"), indices)
}

#[test]
fn scoped_ports_require_prior_signal_initialization_and_keep_input_controls() {
    for (body, available) in [
        ("signal y;x<--y;y<--1;", false),
        ("signal y;var t=y;y<--1;x<--1;", false),
        ("signal y;if(n){y<--1;}x<--y;", false),
        ("signal y[2];y[0]<--1;x<--y[1];", false),
        ("signal input y[2];var t=y[n];x<--1;", false),
        ("signal input y;y<--1;x<--1;", false),
        ("signal input y;x<--y;", true),
        ("signal y;y<--1;x<--y;", true),
        ("signal y[2];y[1]<--1;x<--y[0x1];", true),
        ("signal input y[2];var i=1;var t=y[i];x<--1;", true),
        ("signal y;if(0){log(y);}x<--1;", true),
    ] {
        let source = format!("template T(n){{signal output x;{body}}}");
        let result = scoped_port(&source, None, &[]);
        assert_eq!(result.certified().is_some(), available, "{source}: {result:?}");
        if let Some(summary) = result.certified() {
            assert_eq!(summary.incidence(), Incidence::Zero);
            assert_eq!(summary.fixed_value(), None, "witness values are not constraints");
        }
    }
}

#[test]
fn scoped_ports_check_exact_rank_bounds_and_generated_constraints() {
    let source = "template T(){signal input a;signal output x[2];x[0]<--a;x[1]<==1;}";
    let zero = scoped_port(source, None, &[0]);
    assert_eq!(zero.certified().unwrap().incidence(), Incidence::Zero);
    let fixed = scoped_port(source, None, &[1]);
    assert_eq!(fixed.certified().unwrap().incidence(), Incidence::Must);
    assert!(fixed.certified().unwrap().fixed_value().is_some());
    for indices in [&[][..], &[2][..], &[0, 0][..]] {
        assert!(scoped_port(source, None, indices).unavailable().is_some());
    }
}

#[test]
fn scoped_port_queries_bind_provider_curve_context_and_definition() {
    let source = "template T(){signal output x;x<--1;}template U(){signal output y;y<--1;}";
    let lifted = fixture(source);
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let other = provider.contexts().symbolic_root(lifted.hir.definition("U").unwrap()).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let x = port(&lifted, "x");
    let result = provider.templates().template_port_for_evidence(&facts, &other, x, &[]);
    assert!(result.unavailable().unwrap().contains(&SummaryBlocker::WrongContext));
    let result =
        provider.templates().template_port_for_evidence(&facts, &evidence, port(&lifted, "y"), &[]);
    assert!(result.unavailable().is_some(), "foreign port cannot be certified");
    let other_curve = ProjectAnalysis::build(&lifted, Curve::Bls12_381).unwrap();
    assert!(other_curve
        .templates()
        .template_port_for_evidence(&facts, &evidence, x, &[])
        .unavailable()
        .is_some());
    let copied = fixture(source);
    let other_project = ProjectAnalysis::build(&copied, Curve::Bn254).unwrap();
    assert!(other_project
        .templates()
        .template_port_for_evidence(&facts, &evidence, x, &[])
        .unavailable()
        .is_some());
}

#[test]
fn scoped_port_queries_keep_the_supplied_budget_after_cache_warmup() {
    let lifted = fixture("template T(){signal output x;x<--1;}");
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let x = port(&lifted, "x");
    let complete = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    assert!(provider
        .templates()
        .template_port_for_evidence(&complete, &evidence, x, &[])
        .certified()
        .is_some());
    let exhausted = provider.contexts().analyze_for_evidence(&cfg, &evidence, Some(0)).unwrap();
    assert!(provider
        .templates()
        .template_port_for_evidence(&exhausted, &evidence, x, &[])
        .unavailable()
        .is_some());
    assert!(provider
        .templates()
        .template_port_for_evidence(&complete, &evidence, x, &[])
        .certified()
        .is_some());
}

#[test]
fn scoped_port_queries_preserve_main_but_refuse_incoming_call_closure() {
    let source = concat!(
        "template Child(){signal output y;y<--1;}",
        "template T(){signal output x;x<--1;component c=Child();}component main=T();"
    );
    let lifted = fixture(source);
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(main.id(), provider.hir())
    else {
        panic!("main call must be reachable")
    };
    let evidence = provider.contexts().main_evidence(&main).unwrap();
    let definition = evidence.context().definition();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let x = port(&lifted, "x");
    assert!(provider
        .templates()
        .template_port_for_evidence(&facts, &evidence, x, &[])
        .certified()
        .is_some());
    let symbolic = provider.contexts().symbolic_root(definition).unwrap();
    assert!(provider
        .templates()
        .template_port_for_evidence(&facts, &symbolic, x, &[])
        .unavailable()
        .is_some());
    let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("child call must be reachable")
    };
    let child = provider.contexts().call_evidence(&call, &facts, &evidence).unwrap();
    let cfg = build_cfg(&lifted.hir, child.context().definition()).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &child, None).unwrap();
    let result =
        provider.templates().template_port_for_evidence(&facts, &child, port(&lifted, "y"), &[]);
    assert!(result.unavailable().unwrap().contains(&SummaryBlocker::UnsupportedContext));
}

#[test]
fn constructor_arguments_keep_local_read_checks_and_unknown_calls_abstain() {
    for (body, available) in [
        ("component c=Child(1);x<--1;", true),
        ("signal y;component c=Child(y);y<--1;x<--1;", false),
        ("component c=Missing();x<--1;", false),
        ("component c=Child(1);x<--c.y;", false),
    ] {
        let source = format!(
            "template Child(n){{signal output y;y<--n;}}template T(){{signal output x;{body}}}"
        );
        let result = scoped_port(&source, None, &[]);
        assert_eq!(result.certified().is_some(), available, "{source}: {result:?}");
    }
}

#[test]
fn child_validity_is_checked_before_constructor_read_transparency() {
    for child in [
        "signal a;signal b;b<--a;a<--1;",
        "signal a;signal b;signal c;signal z;a<--1;b<--1;c<--1;\
         z<--a*b+a*c;z===a*b+a*c;",
        "signal s;s<--1;s<--2;",
        "assert(0);",
        "signal input a;signal s;s<--a;",
        "component c=Leaf();",
        "component c=Missing();",
    ] {
        let source = format!(
            "template Leaf(){{signal s;s<--1;}}template Child(){{{child}}}\
             template T(){{signal output x;x<--1;component c=Child();}}"
        );
        let result = scoped_port(&source, None, &[]);
        assert!(result.unavailable().is_some(), "{source}: {result:?}");
    }
    let source = concat!(
        "template Child(){signal a;signal b;signal c;signal z;",
        "a<--1;b<--1;c<--1;z<--(a+b)*c;z===(a+b)*c;}",
        "template T(){signal output x;x<--1;component c=Child();}"
    );
    assert!(scoped_port(source, None, &[]).certified().is_some());
}

#[test]
fn constructor_calls_need_computable_arguments_and_correct_source_kind() {
    for source in [
        "template Child(n){signal s;s<--n;}template T(n){signal output x;x<--1;\
         component c=Child(n);}",
        "function F(){return 1;}template T(){signal output x;x<--1;component c=F();}",
        "pragma custom_templates;template custom Child(){signal s;s<--1;}\
         template T(){signal output x;x<--1;component c=Child();}",
    ] {
        let result = scoped_port(source, None, &[]);
        assert!(result.unavailable().is_some(), "{source}: {result:?}");
    }
}

#[test]
fn constructor_coverage_budget_abstains_instead_of_accepting_a_partial_set() {
    for (count, available) in [(64, true), (65, false)] {
        let mut source =
            String::from("template Child(){signal s;s<--1;}template T(){signal output x;x<--1;");
        for index in 0..count {
            source.push_str(&format!("component c{index}=Child();"));
        }
        source.push('}');
        let result = scoped_port(&source, None, &[]);
        assert_eq!(result.certified().is_some(), available, "count={count}: {result:?}");
        if !available {
            assert!(result.unavailable().unwrap().contains(&SummaryBlocker::ContextBudget));
        }
    }
}

#[test]
fn every_constructor_instance_keeps_its_exact_argument_context() {
    let child =
        concat!("template Child(n){signal a;signal b;", "if(n){b<--a;a<--1;}else{a<--1;b<--a;}}");
    for calls in [
        "component first=Child(0);component second=Child(1);",
        "component first=Child(1);component second=Child(0);",
    ] {
        let source = format!("{child}template T(){{signal output x;x<--1;{calls}}}");
        let fact = scoped_port(&source, None, &[]);
        assert!(fact.unavailable().is_some(), "invalid instance: {fact:?}");
    }
    let source = format!(
        "{child}template T(){{signal output x;x<--1;\
         component first=Child(0);component second=Child(0);}}"
    );
    assert!(scoped_port(&source, None, &[]).certified().is_some());
}

#[test]
fn constant_returning_calls_do_not_hide_signal_dependent_constructor_arguments() {
    for (body, available) in [
        ("signal y;component c=Child(Ignore(y));y<--1;x<--1;", false),
        ("signal y;y<--1;component c=Child(Ignore(y));x<--1;", false),
    ] {
        let source = format!(
            "function Ignore(v){{return 1;}}template Child(n){{signal s;s<--n;}}\
             template T(){{signal output x;{body}}}"
        );
        let fact = scoped_port(&source, None, &[]);
        assert_eq!(fact.certified().is_some(), available, "{source}: {fact:?}");
    }
}
