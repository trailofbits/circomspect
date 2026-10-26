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

use abstract_interpretation::graph::FlowGraph;
use circomspect_program_analysis::hir_cfg::{build_cfg, CfgNodeKind};
use circomspect_program_analysis::hir_facts::{BodyWriteStatus, Fact, FactBlocker, WitnessWriteIssue};
use circomspect_program_analysis::interprocedural::ProjectAnalysis;
use parser::hir::{lift_project, DefinitionRef};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn status(source: &str) -> Fact<BodyWriteStatus> {
    let (fact, diagnostics) = status_with_diagnostics(source);
    assert_eq!(diagnostics, 0, "unexpected semantic diagnostics");
    fact
}

fn status_with_diagnostics(source: &str) -> (Fact<BodyWriteStatus>, usize) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-body-status-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    let diagnostics = lifted.diagnostics.len();
    let definition = lifted.hir.definition("T").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let target = cfg
        .nodes()
        .iter()
        .find_map(|site| {
            let CfgNodeKind::Witness { target, .. } = &cfg.node(*site)?.kind else {
                return None;
            };
            Some(target)
        })
        .expect("witness write");
    (facts.body_write_status(target), diagnostics)
}

fn port_availability(source: &str, names: &[&str]) -> Vec<bool> {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-body-writes-{}-{:?}",
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
    let DefinitionRef::Template(id) = definition else { panic!("template") };
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let ports = &lifted.hir.template(id).unwrap().ports;
    names
        .iter()
        .map(|name| {
            let port = ports
                .iter()
                .find(|port| {
                    let symbol = lifted.hir.port(**port).unwrap().symbol;
                    lifted.hir.symbol(symbol).unwrap().name == **name
                })
                .unwrap();
            provider.template_port(id, evidence.context(), *port).certified().is_some()
        })
        .collect()
}

fn assert_no_repeat(fact: &Fact<BodyWriteStatus>) {
    let Some(BodyWriteStatus::NoRepeat(_)) = fact.certified() else {
        panic!("expected a no-repeat certificate: {fact:?}");
    };
}

fn has_write_blocker(fact: &Fact<BodyWriteStatus>, expected: WitnessWriteIssue) -> bool {
    fact.unavailable().is_some_and(|blockers| {
        blockers.iter().any(|blocker| {
            let FactBlocker::WitnessWrite(_, actual) = blocker else {
                return false;
            };
            *actual == expected
        })
    })
}

#[test]
fn repeated_body_write_blocks_independent_port_summary() {
    let source = "template T(){signal input a;signal output x;x<--a;x<==a;}";
    assert_eq!(port_availability(source, &["x"]), [false]);
}

#[test]
fn possible_repeat_blocks_only_its_port_summary() {
    let source = "template T(n){signal output x;signal output y;\
                  if(n){x<--1;}x<==2;y<==3;}";
    assert_eq!(port_availability(source, &["x", "y"]), [false, true]);
}

#[test]
fn one_generated_assignment_is_one_body_write() {
    let fact = status("template T(){signal output x;x<==1;}");
    assert_no_repeat(&fact);
}

#[test]
fn exact_array_elements_are_distinct_but_a_repeated_element_fails() {
    let distinct = status("template T(){signal output x[2];x[0]<--1;x[1]<--2;}");
    assert_no_repeat(&distinct);
    let source = "template T(){signal output x[2];x[0]<--1;x[0]<--2;}";
    let repeated = status(source);
    let Some(BodyWriteStatus::DefinitelyRepeated(certificate)) = repeated.certified() else {
        panic!("second exact write must repeat the first: {repeated:?}");
    };
    let site = certificate.sites()[0].span;
    assert_eq!(&source[site.start()..site.end()], "x[0]<--2");
}

#[test]
fn exclusive_branch_writes_do_not_count_as_repeated() {
    let source = "template T(n){signal output x;if(n){x<--1;}else{x<--2;}}";
    let fact = status(source);
    assert_no_repeat(&fact);
}

#[test]
fn post_join_write_distinguishes_possible_from_definite_repeat() {
    let possible = status("template T(n){signal output x;if(n){x<--1;}x<--2;}");
    assert!(has_write_blocker(&possible, WitnessWriteIssue::PossibleRepeat));
    let definite = status("template T(n){signal output x;if(n){x<--1;}else{x<--2;}x<--3;}");
    let Some(BodyWriteStatus::DefinitelyRepeated(_)) = definite.certified() else {
        panic!("expected a definite repeat certificate: {definite:?}");
    };
}

#[test]
fn unresolved_index_can_alias_exact_element_and_blocks_no_repeat() {
    let source = "template T(){signal input i;signal output x[2];x[0]<--1;x[i]<--2;}";
    let fact = status(source);
    assert!(has_write_blocker(&fact, WitnessWriteIssue::UnresolvedTarget));
}

#[test]
fn opaque_assignment_without_a_retained_target_blocks_no_repeat() {
    let source = "template T(){signal output x;x<--1;x<--Missing();}";
    let (fact, diagnostics) = status_with_diagnostics(source);
    assert!(diagnostics > 0);
    assert!(has_write_blocker(&fact, WitnessWriteIssue::UnresolvedTarget));
}

#[test]
fn independent_literal_loops_preserve_body_write_multiplicity() {
    for source in [
        "template T(){signal output x;x<--1;if(0){x<--2;}}",
        "template T(){signal output x;for(var i=0;i<1;i++){x<--i;}}",
    ] {
        let fact = status(source);
        let Some(BodyWriteStatus::NoRepeat(_)) = fact.certified() else {
            panic!("{source}: {fact:?}");
        };
    }
    let source = "template T(){signal output x;for(var i=0;i<2;i++){x<--i;}}";
    let fact = status(source);
    let Some(BodyWriteStatus::DefinitelyRepeated(_)) = fact.certified() else {
        panic!("{source}: {fact:?}");
    };
}

#[test]
fn independent_alternative_duplicate_targets_reject_every_port() {
    let source = "template T(n){signal output x;signal output y;signal output z;\
                  if(n){x<--1;x<--2;}else{y<--1;y<--2;}z<==3;}";
    assert_eq!(port_availability(source, &["x", "y", "z"]), [false, false, false]);
}

#[test]
fn independent_one_failing_branch_does_not_prove_whole_body_failure() {
    let source = "template T(n){signal output x;signal output y;\
                  if(n){x<--1;x<--2;}else{x<--3;}y<==4;}";
    assert_eq!(port_availability(source, &["x", "y"]), [false, true]);
}
