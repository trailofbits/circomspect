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

use abstract_interpretation::graph::FlowGraph;
use circomspect_program_analysis::hir_cfg::{build_cfg, CfgNodeKind, DefinitionCfg};
use circomspect_program_analysis::hir_facts::{analyze, AnalysisError, FieldContext};
use circomspect_program_analysis::interprocedural::{CallOwner, CallReachability, ProjectSummaries};
use parser::hir::{lift_project, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use parser::frontend::AssignmentOperator;
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-seeded-loop-{}-{:?}",
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

fn loop_nodes(cfg: &DefinitionCfg) -> usize {
    let mut count = 0;
    for id in cfg.nodes() {
        let Some(node) = cfg.node(*id) else { panic!("graph node must exist") };
        if let CfgNodeKind::LoopHeader = node.kind {
            count += 1;
        }
    }
    count
}

fn iteration_trace(cfg: &DefinitionCfg) -> String {
    let mut trace = String::new();
    for id in cfg.nodes() {
        let Some(node) = cfg.node(*id) else { panic!("graph node must exist") };
        if let CfgNodeKind::Branch { .. } = &node.kind {
            trace.push('B');
        } else if let CfgNodeKind::Assignment { operator: AssignmentOperator::Add, .. } = &node.kind
        {
            trace.push('A');
        } else if let CfgNodeKind::Update { .. } = &node.kind {
            trace.push('U');
        }
    }
    trace
}

fn provider_cfg(argument: &str, body: &str) -> DefinitionCfg {
    provider_cfg_with_loop(argument, body, "0", "i++")
}

fn provider_cfg_with_loop(argument: &str, body: &str, initial: &str, step: &str) -> DefinitionCfg {
    let source = format!(
        "template Loop(n){{var sum=0;for(var i={initial};i<n;{step}){{{body}}}}}\
         component main=Loop({argument});"
    );
    provider_cfg_source(&source)
}

fn provider_cfg_source(source: &str) -> DefinitionCfg {
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &lifted.hir)
    else {
        panic!("main must be reachable");
    };
    let evidence = provider.main_evidence(&call).unwrap();
    let baseline = build_cfg(&lifted.hir, evidence.context().definition()).unwrap();
    assert_eq!(loop_nodes(&baseline), 1);
    let facts = provider.analyze_for_evidence(&baseline, &evidence, None).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let Err(error) = analyze(&lifted.hir, facts.cfg(), &field, None) else {
        panic!("specialized graph cannot be reanalyzed without its scalar seeds");
    };
    assert_eq!(error, AnalysisError::WrongScalarSeeds);
    facts.cfg().clone()
}

#[test]
fn provider_scalar_bound_unrolls_existing_cfg_in_source_order() {
    for (bound, count) in [("0", 0), ("3", 3), ("64", 64), ("254", 254), ("512", 512)] {
        let cfg = provider_cfg(bound, "sum+=i;");
        assert_eq!(loop_nodes(&cfg), 0, "bound {bound}");
        assert_eq!(iteration_trace(&cfg), format!("{}B", "BAU".repeat(count)));
    }
}

#[test]
fn unsupported_or_nonterminating_bounds_keep_a_real_loop() {
    for bound in ["513", "0-1"] {
        let cfg = provider_cfg(bound, "sum+=i;");
        assert_eq!(loop_nodes(&cfg), 1, "bound {bound}");
    }
}

#[test]
fn symbolic_library_parameter_keeps_a_real_loop() {
    let lifted = fixture("template Loop(n){var sum=0;for(var i=0;i<n;i++){sum+=i;}}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("Loop").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    assert_eq!(loop_nodes(facts.cfg()), 1);
}

#[test]
fn body_write_to_induction_variable_withholds_unrolling() {
    let cfg = provider_cfg("3", "i++;sum+=i;");
    assert_eq!(loop_nodes(&cfg), 1);
}

#[test]
fn mutable_parameter_cannot_supply_a_static_loop_bound() {
    for write in ["n=0;", "n+=1;"] {
        let source = format!(
            "template Loop(n){{var sum=0;{write}for(var i=0;i<n;i++){{sum+=i;}}}}\
             component main=Loop(3);"
        );
        let cfg = provider_cfg_source(&source);
        assert_eq!(loop_nodes(&cfg), 1, "write {write}");
    }
}

#[test]
fn nonunit_and_nonterminating_steps_keep_a_real_loop() {
    for step in ["i+=2", "i--"] {
        let cfg = provider_cfg_with_loop("3", "sum+=i;", "0", step);
        assert_eq!(loop_nodes(&cfg), 1, "step {step}");
    }
}

#[test]
fn nonzero_initial_value_limits_the_executed_iterations() {
    let cfg = provider_cfg_with_loop("3", "sum+=i;", "1", "i++");
    assert_eq!(loop_nodes(&cfg), 0);
    assert_eq!(iteration_trace(&cfg), "BAUBAUB");
}

#[test]
fn exceeded_cfg_budget_retains_a_real_loop() {
    let body = "sum+=1;".repeat(400);
    let cfg = provider_cfg("512", &body);
    assert_eq!(loop_nodes(&cfg), 1);
}

#[test]
fn unrelated_library_size_does_not_change_a_tiny_bound_loop() {
    let template = "template Loop(n){var sum=0;for(var i=0;i<n;i++){sum+=i;}}";
    let base = format!("{template}component main=Loop(254);");
    assert_eq!(loop_nodes(&provider_cfg_source(&base)), 0);

    let mut unrelated = String::from("template Unrelated(){");
    for index in 0..300 {
        unrelated.push_str(&format!("var value{index}=0;"));
    }
    unrelated.push('}');
    let expanded = format!("{template}{unrelated}component main=Loop(254);");
    assert_eq!(loop_nodes(&provider_cfg_source(&expanded)), 0);
}
