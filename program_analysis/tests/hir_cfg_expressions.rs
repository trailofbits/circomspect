use std::collections::BTreeSet;
use std::fs;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use circomspect_program_analysis::hir_cfg::{build_cfg, CfgNodeKind, DefinitionCfg, EdgeKind};
use parser::hir::{lift_project, ControlGuard, DefinitionRef, LiftedProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};

fn fixture(source: &str) -> (LiftedProject, DefinitionRef) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-cfg-expressions-{}-{:?}",
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
    let definition = lifted.hir.definition("Check").unwrap();
    (lifted, definition)
}

fn text(source: &str, cfg: &DefinitionCfg, node: NodeId) -> String {
    let origin = cfg.node(node).unwrap().origin.unwrap();
    source[origin.span.start()..origin.span.end()].to_string()
}

fn evaluation_paths(source: &str, cfg: &DefinitionCfg) -> BTreeSet<Vec<String>> {
    let mut paths = BTreeSet::new();
    let mut pending = vec![(cfg.entry(), Vec::new())];
    while let Some((node, mut path)) = pending.pop() {
        if let CfgNodeKind::Evaluate(_) = cfg.node(node).unwrap().kind {
            path.push(text(source, cfg, node));
        }
        if node == cfg.exit() {
            paths.insert(path);
            continue;
        }
        for edge in cfg.edges() {
            let edge = cfg.edge(*edge).unwrap();
            if edge.source == node {
                pending.push((edge.target, path.clone()));
            }
        }
    }
    paths
}

#[test]
fn left_associated_512_term_expression_builds_on_the_normal_stack() {
    let mut terms = Vec::new();
    for index in 1..=512 {
        terms.push(format!("{index}*a"));
    }
    let source =
        format!("template Check(){{signal input a;signal output out;out<=={};}}", terms.join("+"));
    let (lifted, definition) = fixture(&source);
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let paths = evaluation_paths(&source, &cfg);
    assert_eq!(paths.len(), 1);
    let path = paths.first().unwrap();
    assert_eq!(&path[..6], ["1", "a", "1*a", "2", "a", "2*a"]);
    assert_eq!(path.last().unwrap(), &terms.join("+"));
}

#[test]
fn nested_ternary_call_and_index_evaluation_preserve_path_order() {
    let source = concat!(
        "function F(a,b){return a+b;}",
        "template Check(n,m){var i=0;var a[2];",
        "var out=n?F(a[i],m?1:2):F(3,4);var after=7;}"
    );
    let (lifted, definition) = fixture(source);
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let paths = evaluation_paths(source, &cfg);
    let expected: BTreeSet<Vec<String>> = [
        vec![
            "0",
            "2",
            "n",
            "i",
            "a[i]",
            "m",
            "1",
            "m?1:2",
            "F(a[i],m?1:2)",
            "n?F(a[i],m?1:2):F(3,4)",
            "7",
        ],
        vec![
            "0",
            "2",
            "n",
            "i",
            "a[i]",
            "m",
            "2",
            "m?1:2",
            "F(a[i],m?1:2)",
            "n?F(a[i],m?1:2):F(3,4)",
            "7",
        ],
        vec!["0", "2", "n", "3", "4", "F(3,4)", "n?F(a[i],m?1:2):F(3,4)", "7"],
    ]
    .into_iter()
    .map(|path| path.into_iter().map(String::from).collect())
    .collect();
    assert_eq!(paths, expected);
}

#[test]
fn nested_deferred_controls_end_at_their_own_ternary_values() {
    let source = "template Check(n,m){var out=n?(m?1:2):3;var after=7;}";
    let (lifted, definition) = fixture(source);
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let mut branches = Vec::new();
    for id in cfg.nodes() {
        let node = cfg.node(*id).unwrap();
        if let CfgNodeKind::Branch { guard, .. } = node.kind {
            assert_eq!(guard, ControlGuard::DeferredScalar);
            branches.push(*id);
        }
    }
    assert_eq!(branches.len(), 2);
    for id in cfg.nodes() {
        let node = cfg.node(*id).unwrap();
        let CfgNodeKind::Evaluate(expression) = node.kind else { continue };
        let origin = node.origin.unwrap();
        assert_eq!(origin.expression, Some(expression));
        assert_eq!(origin.span, lifted.hir.expression(expression).unwrap().span);
        let expected = match text(source, &cfg, *id).as_str() {
            "n" | "7" => BTreeSet::new(),
            "m" | "3" | "n?(m?1:2):3" => BTreeSet::from([branches[0]]),
            "1" | "2" | "m?1:2" => BTreeSet::from([branches[0], branches[1]]),
            unexpected => panic!("unexpected evaluation {unexpected}"),
        };
        assert_eq!(node.deferred_controls, expected, "{}", text(source, &cfg, *id));
    }
    for branch in branches {
        let edges: Vec<_> = cfg
            .edges()
            .iter()
            .filter_map(|edge| {
                let edge = cfg.edge(*edge).unwrap();
                (edge.source == branch).then_some(edge)
            })
            .collect();
        assert_eq!(edges.len(), 2);
        assert_eq!(edges[0].payload.kind, EdgeKind::True);
        assert_eq!(edges[1].payload.kind, EdgeKind::False);
        for edge in edges {
            assert_eq!(edge.payload.guard, Some(ControlGuard::DeferredScalar));
        }
    }
}

#[test]
fn multiple_indices_and_nested_call_arguments_keep_left_to_right_order() {
    let source = concat!(
        "function F(a,b){return a+b;}template Check(){var i=0;var j=1;var a[2][2];",
        "var x=F(a[i][j],-F(3,4));}"
    );
    let (lifted, definition) = fixture(source);
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let expected = [
        "0",
        "1",
        "2",
        "2",
        "i",
        "j",
        "a[i][j]",
        "3",
        "4",
        "F(3,4)",
        "-F(3,4)",
        "F(a[i][j],-F(3,4))",
    ];
    assert_eq!(
        evaluation_paths(source, &cfg),
        BTreeSet::from([expected.into_iter().map(String::from).collect()])
    );
}

#[test]
fn array_items_keep_nested_argument_order() {
    let source = "function F(a,b){return a+b;}template Check(){var a[2]=[F(1,2),F(3,4)];}";
    let (lifted, definition) = fixture(source);
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let expected = ["2", "1", "2", "F(1,2)", "3", "4", "F(3,4)", "[F(1,2),F(3,4)]"];
    assert_eq!(
        evaluation_paths(source, &cfg),
        BTreeSet::from([expected.into_iter().map(String::from).collect()])
    );
}

#[test]
fn compile_time_ternary_does_not_add_a_deferred_control() {
    let source = "template Check(n){var out=n?(1?2:3):4;var after=7;}";
    let (lifted, definition) = fixture(source);
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let deferred = cfg
        .nodes()
        .iter()
        .find_map(|id| {
            let CfgNodeKind::Branch { guard: ControlGuard::DeferredScalar, .. } =
                cfg.node(*id).unwrap().kind
            else {
                return None;
            };
            Some(*id)
        })
        .unwrap();
    let mut saw_constant_branch = false;
    for id in cfg.nodes() {
        let node = cfg.node(*id).unwrap();
        if let CfgNodeKind::Branch { guard: ControlGuard::CheckedCompileTime, .. } = node.kind {
            saw_constant_branch = true;
            assert_eq!(node.deferred_controls, BTreeSet::from([deferred]));
        }
        let CfgNodeKind::Evaluate(_) = node.kind else { continue };
        if ["1", "2", "3", "1?2:3", "4", "n?(1?2:3):4"].contains(&text(source, &cfg, *id).as_str())
        {
            assert_eq!(node.deferred_controls, BTreeSet::from([deferred]));
        }
        if text(source, &cfg, *id) == "7" {
            assert!(node.deferred_controls.is_empty());
        }
    }
    assert!(saw_constant_branch);
}

#[test]
fn anonymous_constructor_evaluates_parameters_before_input_values() {
    let source = concat!(
        "template C(a,b){signal input x;signal input y;signal output z;z<==a+b+x+y;}",
        "template Check(){signal output z;z<==C(1,2)(3,4);}"
    );
    let (lifted, definition) = fixture(source);
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let paths = evaluation_paths(source, &cfg);
    let expected = ["1", "2", "3", "4", "C(1,2)(3,4)"];
    assert_eq!(paths, BTreeSet::from([expected.into_iter().map(String::from).collect()]));
}
