use std::collections::BTreeSet;
use std::fs;

use parser::hir::lift_project;
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::build_cfg;
use crate::hir_facts::relations::complete::ProofBudget;
use crate::hir_facts::relations::NormalizedEquation;
use crate::hir_facts::FactBlocker;
use crate::interprocedural::ProjectSummaries;

#[derive(Debug)]
struct Snapshot {
    sources: Vec<String>,
    equations: Vec<NormalizedEquation>,
    key_count: usize,
}

fn inspect(
    source: &str,
    solver_budget: Option<usize>,
    proof_budget: &mut ProofBudget,
) -> Result<Snapshot, BTreeSet<FactBlocker>> {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-equation-sites-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty());
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, solver_budget).unwrap();
    let result = facts.generated_equation_sites(proof_budget);
    let Some(sites) = result.certified() else {
        return Err(result.unavailable().unwrap().clone());
    };
    let mut sources = Vec::new();
    let mut equations = Vec::new();
    for site in sites.sites() {
        let span = site.origin().span;
        sources.push(source[span.start()..span.end()].to_owned());
        equations.push(site.equation().clone());
    }
    Ok(Snapshot { sources, equations, key_count: sites.keys().len() })
}

fn collect(source: &str) -> Snapshot {
    inspect(source, None, &mut ProofBudget::default()).unwrap()
}

#[test]
fn collector_retains_additional_constraints_and_duplicate_source_origins() {
    let source = "template T(){signal input a;signal input b;a*(a-1)===0;\
                  b*(b-1)===0;a===b;a===0;a===0;}";
    let result = collect(source);
    assert_eq!(result.sources, ["a*(a-1)===0;", "b*(b-1)===0;", "a===b;", "a===0;", "a===0;"]);
    assert_eq!(result.equations[3], result.equations[4]);
    assert_eq!(result.key_count, 2);
}

#[test]
fn collector_preserves_may_equations_lost_by_exit_intersection() {
    let source = "template T(n){signal input a;a*(a-1)===0;if(n){a===0;}else{a===1;}}";
    let result = collect(source);
    assert_eq!(result.sources, ["a*(a-1)===0;", "a===0;", "a===1;"]);
    assert_ne!(result.equations[1], result.equations[2]);
}

#[test]
fn collector_uses_each_sites_variable_state_before_later_changes() {
    let source = "template T(){signal input a;var k=1;a===k;k=2;a===k;}";
    let result = collect(source);
    assert_eq!(result.sources, ["a===k;", "a===k;"]);
    assert_ne!(result.equations[0], result.equations[1]);
}

#[test]
fn only_certified_dead_constraints_are_excluded() {
    let source = "template T(){signal input a;if(0){a===a*a*a;}if(1){a===0;}else{a===1;}}";
    let result = collect(source);
    assert_eq!(result.sources, ["a===0;"]);
}

#[test]
fn generated_assignment_and_constant_contradiction_are_both_collected() {
    let result = collect("template T(){signal output a;a<==0;0===1;}");
    assert_eq!(result.sources, ["a<==0", "0===1;"]);
    assert_eq!(result.key_count, 1);
}

#[test]
fn witness_assignments_never_enter_the_generated_site_collection() {
    let result = collect("template T(){signal a;a<--1;}");
    assert!(result.sources.is_empty());
    assert_eq!(result.key_count, 0);
}

#[test]
fn unsupported_generated_forms_and_unchecked_indices_block_collection() {
    for source in [
        "template T(){signal input a;signal input b;signal input c;a*b+a*c===0;}",
        "template T(){signal input a;a*a*a===0;}",
        "template T(n){signal input a[2];a[n]===0;}",
        "template T(){signal input a[1];a[1]===0;}",
        "template T(){signal input a;a===Missing();}",
    ] {
        let result = inspect(source, None, &mut ProofBudget::default());
        assert!(result.is_err(), "{source}: {result:?}");
    }
}

#[test]
fn equation_cancellation_does_not_erase_invalid_source_accesses() {
    let source = "template T(){signal input a[1];a[1]-a[1]===0;}";
    let result = inspect(source, None, &mut ProofBudget::default());
    assert!(result.is_err(), "{result:?}");
}

#[test]
fn complete_sites_remain_local_when_an_unrelated_definition_is_broken() {
    let result = collect("template T(){signal input a;a===0;}template Broken(){var x=Missing();}");
    assert_eq!(result.sources, ["a===0;"]);
}

#[test]
fn incomplete_solver_and_proof_limits_never_return_partial_sites() {
    let source = "template T(){signal input a;signal input b;a===0;b===0;}";
    assert!(inspect(source, Some(0), &mut ProofBudget::default()).is_err());
    for budget in [
        ProofBudget::limited(1, 16, 16, 32),
        ProofBudget::limited(16, 1, 16, 32),
        ProofBudget::limited(16, 16, 1, 32),
    ] {
        let mut budget = budget;
        let result = inspect(source, None, &mut budget);
        assert!(result.is_err(), "{result:?}");
    }
    assert_eq!(collect(source).sources, ["a===0;", "b===0;"]);
}

#[test]
fn every_cfg_node_consumes_collection_budget_even_without_constraints() {
    for source in ["template T(){var a=0;var b=1;}", "template T(){if(0){var a=0;var b=1;}}"] {
        let result = inspect(source, None, &mut ProofBudget::limited(16, 16, 16, 1));
        assert!(result.is_err(), "{source}: {result:?}");
        assert!(collect(source).sources.is_empty());
    }
}
