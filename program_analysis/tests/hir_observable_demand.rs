use std::fs;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use circomspect_program_analysis::hir_cfg::{build_cfg, CfgNodeKind};
use circomspect_program_analysis::hir_facts::{AssignmentDemand, Fact, FactBlocker};
use circomspect_program_analysis::interprocedural::{ProjectSummaries, SummaryBlocker};
use circomspect_program_analysis::new_rules::RuleContext;
use parser::hir::lift_project;
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

type DemandResult = Result<Fact<AssignmentDemand>, SummaryBlocker>;

fn assignment_demands(source: &str, budget: Option<usize>) -> Vec<(String, DemandResult)> {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-demand-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("Check").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, budget).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    let mut demands = Vec::new();
    for id in facts.cfg().nodes() {
        let Some(node) = facts.cfg().node(*id) else { continue };
        let CfgNodeKind::Assignment { target, .. } = &node.kind else { continue };
        let Some(symbol) = lifted.hir.symbol(target.root) else { continue };
        demands.push((symbol.name.clone(), context.assignment_demand(*id, target)));
    }
    demands
}

fn unobserved(result: &DemandResult) -> bool {
    let Ok(fact) = result else { return false };
    let Some(AssignmentDemand::Unobserved(_)) = fact.certified() else { return false };
    true
}

#[test]
fn dead_scalar_chain_is_unobserved_and_returned_chain_is_required() {
    let dead = assignment_demands("function Check(){var x=1;var y=x;return 7;}", None);
    assert_eq!(dead.len(), 2);
    assert!(dead.iter().all(|(_, result)| unobserved(result)));

    let returned = assignment_demands("function Check(){var x=1;var y=x;return y;}", None);
    assert_eq!(returned.len(), 2);
    assert!(returned.iter().all(|(_, result)| {
        let Ok(fact) = result else { return false };
        let Some(AssignmentDemand::MayBeObserved) = fact.certified() else { return false };
        true
    }));
}

#[test]
fn required_assertion_and_witness_effect_keep_their_input_chain() {
    for source in [
        "function Check(){var x=1;var y=x;assert(y);return 7;}",
        "template Check(){var x=1;var y=x;signal output z;z<==y;}",
    ] {
        let results = assignment_demands(source, None);
        assert_eq!(results.len(), 2);
        assert!(results.iter().all(|(_, result)| !unobserved(result)), "{source}");
    }
}

#[test]
fn overwritten_versions_and_pruned_branches_preserve_exact_demand() {
    let overwritten = assignment_demands("function Check(){var x=1;x=2;return x;}", None);
    assert_eq!(overwritten.len(), 2);
    assert!(unobserved(&overwritten[0].1));
    assert!(!unobserved(&overwritten[1].1));

    let dead_branch =
        assignment_demands("function Check(){var x=1;if(0){assert(x);}return 7;}", None);
    assert_eq!(dead_branch.len(), 1);
    assert!(unobserved(&dead_branch[0].1));
    let live_branch =
        assignment_demands("function Check(){var x=1;if(1){assert(x);}return 7;}", None);
    assert_eq!(live_branch.len(), 1);
    assert!(!unobserved(&live_branch[0].1));
}

#[test]
fn declaration_dimensions_and_log_values_observe_local_inputs() {
    for source in [
        "function Check(){var x=1;var a[x];return 7;}",
        "function Check(){var x=1;log(x);return 7;}",
    ] {
        let results = assignment_demands(source, None);
        assert!(!results.is_empty(), "{source}");
        assert!(!unobserved(&results[0].1), "{source}");
    }
}

#[test]
fn unsafe_reads_and_budgeted_analysis_cannot_prove_no_demand() {
    let signal_read = assignment_demands("template Check(){signal input s;var x=s;}", None);
    assert_eq!(signal_read.len(), 1);
    assert!(!unobserved(&signal_read[0].1));

    let call = assignment_demands(
        "function F(n){assert(n);return 7;}function Check(){var x=1;var y=F(x);return 7;}",
        None,
    );
    assert!(!call.is_empty());
    assert!(!unobserved(&call[0].1));

    let budget = assignment_demands("function Check(){var x=1;var y=x;return 7;}", Some(0));
    assert_eq!(budget.len(), 2);
    for (_, result) in &budget {
        let Ok(fact) = result else { panic!("budget must remain a local fact blocker") };
        let Some(blockers) = fact.unavailable() else { panic!("provisional demand was certified") };
        assert!(blockers.iter().any(|blocker| {
            let FactBlocker::Budget(_) = blocker else { return false };
            true
        }));
    }

    let symbolic_index = assignment_demands("template Check(i){var x=1;var a[2];a[i]=x;}", None);
    assert!(!symbolic_index.is_empty());
    assert!(!unobserved(&symbolic_index[0].1));
}

#[test]
fn known_failure_refuses_scope_even_when_local_demand_would_be_empty() {
    let results = assignment_demands("function Check(){assert(0);var x=1;return 7;}", None);
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].1, Err(SummaryBlocker::UnsupportedContext));

    let incomplete = assignment_demands("function Check(n){var x=1;var y=~n;return 7;}", None);
    assert!(!incomplete.is_empty());
    assert_eq!(incomplete[0].1, Err(SummaryBlocker::IncompleteDefinition));
}

#[test]
fn loop_edges_converge_and_pruned_loop_reads_do_not_create_demand() {
    let pruned =
        assignment_demands("function Check(){var x=1;while(0){assert(x);}return 7;}", None);
    assert_eq!(pruned.len(), 1);
    assert!(unobserved(&pruned[0].1));

    let live = assignment_demands(
        "function Check(){var x=1;var i=0;while(i<2){i=i+1;assert(x);}return 7;}",
        None,
    );
    assert!(!live.is_empty());
    assert_eq!(live[0].0, "x");
    assert!(!unobserved(&live[0].1));
}

#[test]
fn assignment_query_requires_matching_node_and_source_path() {
    let source = "function Check(){var x=1;var y=2;return 7;}";
    let directory =
        std::env::temp_dir().join(format!("circomspect-demand-foreign-{}", std::process::id()));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("Check").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    let assignments: Vec<_> = facts
        .cfg()
        .nodes()
        .iter()
        .filter_map(|id| {
            let node = facts.cfg().node(*id)?;
            let CfgNodeKind::Assignment { target, .. } = &node.kind else { return None };
            Some((*id, target))
        })
        .collect();
    assert_eq!(assignments.len(), 2);
    let (first, first_path) = assignments[0];
    let (_, second_path) = assignments[1];
    let wrong_path = context.assignment_demand(first, second_path).unwrap();
    assert_eq!(
        wrong_path.unavailable(),
        Some(&std::collections::BTreeSet::from([FactBlocker::ForeignQuery,]))
    );
    let wrong_node = context.assignment_demand(NodeId::new(usize::MAX), first_path).unwrap();
    assert_eq!(wrong_node.unavailable(), wrong_path.unavailable());
    let valid = context.assignment_demand(first, first_path).unwrap();
    let Some(AssignmentDemand::Unobserved(proof)) = valid.certified() else {
        panic!("source-matched assignment must have a typed proof")
    };
    assert_eq!(proof.definition(), definition);
    assert_eq!(proof.context(), context.call_context());
    assert_eq!(proof.node(), first);
    assert_eq!(proof.span(), first_path.span);
}

#[test]
fn independent_shadowed_local_demand_stays_with_the_used_symbol() {
    let results = assignment_demands("function Check(){var x=1;{var x=2;var y=x;}return x;}", None);
    assert_eq!(results.len(), 3);
    let Ok(fact) = &results[0].1 else { panic!("outer x must be certified") };
    assert_eq!(fact.certified(), Some(&AssignmentDemand::MayBeObserved));
    assert!(unobserved(&results[1].1));
    assert!(unobserved(&results[2].1));
}

#[test]
fn independent_branch_join_preserves_demand_from_either_successor() {
    let required =
        assignment_demands("function Check(){var x=1;var y=2;if(1<<1){y=x;}return y;}", None);
    assert_eq!(required.len(), 3);
    for (_, result) in &required {
        let Ok(fact) = result else { panic!("branch inputs must have certified demand") };
        assert_eq!(fact.certified(), Some(&AssignmentDemand::MayBeObserved));
    }
    let unused =
        assignment_demands("function Check(){var x=1;var y=2;if(1<<1){y=x;}return 7;}", None);
    assert_eq!(unused.len(), 3);
    assert!(unused.iter().all(|(_, result)| unobserved(result)));
}

#[test]
fn independent_self_copy_follows_observation_without_creating_demand() {
    let unused = assignment_demands("function Check(){var x=1;x=x;return 7;}", None);
    assert_eq!(unused.len(), 2);
    assert!(unused.iter().all(|(_, result)| unobserved(result)));
    let required = assignment_demands("function Check(){var x=1;x=x;return x;}", None);
    assert_eq!(required.len(), 2);
    for (_, result) in required {
        let Ok(fact) = result else { panic!("self-copy must retain observed demand") };
        assert_eq!(fact.certified(), Some(&AssignmentDemand::MayBeObserved));
    }
}
