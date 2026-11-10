use abstract_interpretation::graph::FlowGraph;
use parser::frontend::{parse_source, LoadedProject, SourceFile, SourceId, Version, VersionPolicy};
use parser::hir::{lift_project, BusId, BusTarget, LiftedProject};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::{build_cfg, CfgNodeKind};
use crate::hir_facts::{analyze, AnalysisFacts, FieldContext};
use crate::interprocedural::execution_scope::{required_node, ExecutionQueries};
use crate::interprocedural::ProjectAnalysis;

fn project(source: &str) -> LiftedProject {
    let id = SourceId::new(0);
    let policy = VersionPolicy::new(Version::new(2, 2, 3));
    let loaded = LoadedProject {
        policy,
        diagnostics: Vec::new(),
        files: vec![SourceFile {
            id,
            path: "execution-scan.circom".into(),
            text: source.into(),
            outcome: parse_source(id, source, policy),
        }],
    };
    let project = lift_project(&loaded);
    assert!(project.syntax_diagnostics.is_empty(), "{:?}", project.syntax_diagnostics);
    project
}

fn reference_failure_scan(
    queries: &ExecutionQueries<'_, '_>,
    facts: &AnalysisFacts<'_>,
    buses: &mut Vec<BusId>,
) -> bool {
    if facts.definitely_repeats_any_body_write().certified() == Some(&true) {
        return true;
    }
    for id in facts.cfg().nodes() {
        if facts.reachable_node(*id).certified() != Some(&true) {
            continue;
        }
        let Some(node) = facts.cfg().node(*id) else { continue };
        if let CfgNodeKind::Declaration { symbol } = &node.kind {
            let symbol = queries.analysis.hir().symbol(*symbol).unwrap();
            if let Some(BusTarget::Bus(id)) = &symbol.bus_type {
                let bus = queries.analysis.hir().bus(*id).unwrap();
                if bus.parameters.is_empty() && symbol.bus_arguments.is_empty() {
                    buses.push(*id);
                }
            }
        }
        if queries.node_definitely_fails(&node.kind, facts) {
            return true;
        }
    }
    false
}

fn reference_required_failure(
    queries: &ExecutionQueries<'_, '_>,
    facts: &AnalysisFacts<'_>,
) -> bool {
    for id in facts.cfg().nodes() {
        if !required_node(facts, *id) {
            continue;
        }
        let Some(node) = facts.cfg().node(*id) else { continue };
        if queries.node_definitely_fails(&node.kind, facts) {
            return true;
        }
    }
    false
}

fn compare_scans(source: &str) {
    let project = project(source);
    let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let queries = provider.execution();
    let cfg = build_cfg(&project.hir, project.hir.definition("T").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    for budget in [Some(0), Some(1), Some(2), Some(8), Some(cfg.nodes().len() * 4), None] {
        let expected_facts = analyze(&project.hir, &cfg, &field, budget).unwrap();
        let actual_facts = analyze(&project.hir, &cfg, &field, budget).unwrap();
        let mut expected_buses: Vec<_> = project.hir.buses().iter().map(|bus| bus.id).collect();
        let mut actual_buses = expected_buses.clone();
        let expected = reference_failure_scan(&queries, &expected_facts, &mut expected_buses);
        let actual = queries.has_proven_failure(&actual_facts, &mut actual_buses);
        assert_eq!((actual, actual_buses), (expected, expected_buses), "{source}, {budget:?}");
        assert_eq!(
            queries.required_local_failure(&actual_facts),
            reference_required_failure(&queries, &expected_facts),
            "{source}, {budget:?}",
        );
    }
}

#[test]
fn candidate_scans_preserve_failure_and_requiredness_across_budgets() {
    for statement in [
        "var x=1;",
        "assert(0);",
        "assert(n);",
        "var x=1/0;",
        "var x=1\\0;",
        "var x=1%0;",
        "var x[-1];",
        "var x[1];x[1]=2;",
        "var x[1];var y=x[1];",
        "var x=Missing();",
    ] {
        compare_scans(&format!("function T(n){{{statement}return 1;}}"));
        compare_scans(&format!("function T(n){{if(0){{{statement}}}return 1;}}"));
        compare_scans(&format!("function T(n){{if(n){{{statement}}}return 1;}}"));
    }
}

const BUSES: &str = "bus A(){signal a;}bus B(){signal b;}bus P(n){signal p[n];}";

#[test]
fn candidate_scans_preserve_pending_bus_prefix_order_and_duplicates() {
    for statements in [
        "A() first;B() second;A() third;P(2) parameterized;",
        "A() first;B() broken[-1];A() after;",
        "if(0){A() dead;}B() live;",
        "if(n){A() conditional;}B() live;",
        "A() before;assert(0);B() after;",
        "A() before;signal x;x<--1;x<--2;B() after;",
    ] {
        compare_scans(&format!("{BUSES}template T(n){{{statements}}}"));
    }
    compare_scans("bus A(){signal a;}bus T(){A() first;A() second;signal bad[-1];}");
}

#[test]
fn a_reachable_failing_bus_declaration_is_enqueued_before_failure() {
    let project = project(&format!("{BUSES}template T(){{A() first;B() broken[-1];A() after;}}"));
    let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let cfg = build_cfg(&project.hir, project.hir.definition("T").unwrap()).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&project.hir, &cfg, &field, None).unwrap();
    let mut pending = Vec::new();
    assert!(provider.execution().has_proven_failure(&facts, &mut pending));
    let names: Vec<_> =
        pending.iter().map(|id| project.hir.bus(*id).unwrap().name.as_str()).collect();
    assert_eq!(names, ["A", "B"]);
}
