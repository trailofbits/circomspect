// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(clippy::allow_attributes, clippy::assert_is_empty, clippy::expect_used, clippy::panic)]

use circomspect_parser::frontend::{
    load_sources, parse_source, tokenize, DiagnosticKind, SourceId, TriviaKind, Version,
    VersionPolicy,
};
use circomspect_parser::hir::{lift_project, AccessStep, Effect, ExprKind, LiftedProject, SemanticCode};
use circomspect_parser::frontend::{AssignmentOperator, InputAssignmentOperator};
use std::path::PathBuf;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/source_compatibility").join(name)
}

fn parse_fixture(name: &str) -> circomspect_parser::frontend::ParseOutcome {
    let text = std::fs::read_to_string(fixture(name)).expect("fixture is readable");
    parse_source(SourceId::new(0), &text, VersionPolicy::new(Version::new(2, 2, 3)))
}

fn lift_fixture(name: &str) -> LiftedProject {
    let project = load_sources(&[fixture(name)], &[], VersionPolicy::new(Version::new(2, 2, 3)));
    assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
    lift_project(&project)
}

fn lift_conformance_fixture(name: &str) -> LiftedProject {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../tests/conformance/cases").join(name);
    let project = load_sources(&[path], &[], VersionPolicy::new(Version::new(2, 2, 3)));
    assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
    lift_project(&project)
}

fn anonymous_output_assignments(lifted: &LiftedProject) -> Vec<(String, String)> {
    let template = lifted
        .hir
        .templates()
        .iter()
        .find(|template| template.name == "Main")
        .expect("Main template");
    let body = lifted.hir.block(template.body).expect("Main body");
    body.effects
        .iter()
        .filter_map(|effect| {
            let (target, value) = match effect {
                Effect::ConstraintAssignment { target, value, .. }
                | Effect::VariableAssignment { target, value, .. } => (target, *value),
                _ => return None,
            };
            let ExprKind::Access(source) = &lifted.hir.expression(value)?.kind else {
                return None;
            };
            let Some(AccessStep::Port { .. }) = source.steps.first() else {
                return None;
            };
            let target = lifted.hir.symbol(target.terminal)?.name.clone();
            let output = lifted.hir.symbol(source.terminal)?.name.clone();
            Some((target, output))
        })
        .collect()
}

#[test]
fn overlapping_comment_opener_uses_the_later_closing_delimiter() {
    let text = std::fs::read_to_string(fixture("comment_overlap_valid.circom"))
        .expect("comment fixture is readable");
    let lexed = tokenize(SourceId::new(0), &text);
    assert!(lexed.diagnostics.is_empty(), "{:?}", lexed.diagnostics);
    let comments: Vec<_> =
        lexed.trivia.iter().filter(|trivia| trivia.kind == TriviaKind::BlockComment).collect();
    assert_eq!(comments.len(), 1);
    let span = comments[0].span;
    assert_eq!(
        &text[span.start()..span.end()],
        "/*// Given the overlapping opening sequence, this whole line is a comment. */"
    );
    assert!(parse_fixture("comment_overlap_valid.circom").diagnostics.is_empty());
}

#[test]
fn overlapping_comment_without_a_later_terminator_is_rejected() {
    let outcome = parse_fixture("comment_overlap_unclosed.circom");
    assert!(outcome
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.kind == DiagnosticKind::UnterminatedComment));
}

#[test]
fn compiler_valid_discard_assignments_do_not_resolve_underscore_as_a_symbol() {
    let project = load_sources(
        &[fixture("discard_valid.circom")],
        &[],
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
    let lifted = lift_project(&project);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    let body = lifted.hir.templates()[0].body;
    let assignments: Vec<_> = lifted
        .hir
        .block(body)
        .expect("template body")
        .effects
        .iter()
        .filter_map(|effect| {
            if let Effect::Discard { operator, .. } = effect {
                Some(*operator)
            } else {
                None
            }
        })
        .collect();
    assert_eq!(
        assignments,
        [
            AssignmentOperator::Assign,
            AssignmentOperator::Witness,
            AssignmentOperator::Constraint,
            AssignmentOperator::ReverseWitness,
            AssignmentOperator::ReverseConstraint,
        ]
    );
}

#[test]
fn signal_discard_in_a_function_is_rejected() {
    let project = load_sources(
        &[fixture("discard_in_function_invalid.circom")],
        &[],
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
    let lifted = lift_project(&project);
    assert!(
        lifted
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == SemanticCode::InvalidAssignment),
        "{:?}",
        lifted.diagnostics
    );
}

#[test]
fn discard_still_validates_its_rhs_call() {
    let project = load_sources(
        &[fixture("discard_invalid_rhs.circom")],
        &[],
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
    let lifted = lift_project(&project);
    assert!(
        lifted.diagnostics.iter().any(|diagnostic| diagnostic.code == SemanticCode::MissingCall),
        "{:?}",
        lifted.diagnostics
    );
}

#[test]
fn tuple_discard_preserves_the_other_assignment() {
    let project = load_sources(
        &[fixture("discard_tuple_valid.circom")],
        &[],
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
    let lifted = lift_project(&project);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    let body = lifted.hir.templates()[0].body;
    let effects = &lifted.hir.block(body).expect("template body").effects;
    let discards: Vec<_> = effects
        .iter()
        .filter_map(|effect| {
            if let Effect::Discard { operator, .. } = effect {
                Some(*operator)
            } else {
                None
            }
        })
        .collect();
    let assignments: Vec<_> = effects
        .iter()
        .filter_map(|effect| {
            if let Effect::ConstraintAssignment { target, .. } = effect {
                Some(target)
            } else {
                None
            }
        })
        .collect();
    assert_eq!(discards, [AssignmentOperator::Constraint]);
    assert_eq!(assignments.len(), 1);
}

#[test]
fn tuple_assignment_with_wrong_arity_is_rejected() {
    let project = load_sources(
        &[fixture("discard_tuple_invalid.circom")],
        &[],
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
    let lifted = lift_project(&project);
    assert!(
        lifted
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == SemanticCode::InvalidAssignment),
        "{:?}",
        lifted.diagnostics
    );
}

#[test]
fn anonymous_multioutput_assignment_binds_each_output_in_order() {
    let lifted = lift_fixture("anonymous_tuple_assignment_valid.circom");
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    assert!(lifted.incomplete.is_empty(), "{:?}", lifted.incomplete);
    assert_eq!(
        anonymous_output_assignments(&lifted),
        [("first".into(), "left".into()), ("second".into(), "right".into())]
    );
}

#[test]
fn anonymous_multioutput_tuple_declarations_bind_each_output_in_order() {
    let lifted = lift_fixture("anonymous_tuple_declaration_valid.circom");
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    assert!(lifted.incomplete.is_empty(), "{:?}", lifted.incomplete);
    assert_eq!(
        anonymous_output_assignments(&lifted),
        [
            ("first".into(), "left".into()),
            ("second".into(), "right".into()),
            ("a".into(), "left".into()),
            ("b".into(), "right".into()),
        ]
    );
}

#[test]
fn anonymous_multioutput_tuple_arity_is_rejected() {
    let lifted = lift_fixture("anonymous_tuple_arity_invalid.circom");
    assert!(
        lifted
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == SemanticCode::InvalidAssignment),
        "{:?}",
        lifted.diagnostics
    );
}

#[test]
fn incomplete_anonymous_inputs_do_not_prove_output_assignments() {
    let lifted = lift_fixture("anonymous_tuple_missing_input_invalid.circom");
    assert!(
        lifted.diagnostics.iter().any(|diagnostic| diagnostic.code == SemanticCode::AnonymousInput),
        "{:?}",
        lifted.diagnostics
    );
    assert!(
        lifted
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != SemanticCode::InvalidAssignment),
        "{:?}",
        lifted.diagnostics
    );
}

#[test]
fn nested_tuple_assignments_preserve_all_three_targets() {
    for name in ["nested_tuple_assignment_valid.circom", "flattened_tuple_assignment_valid.circom"]
    {
        let lifted = lift_fixture(name);
        assert!(lifted.diagnostics.is_empty(), "{name}: {:?}", lifted.diagnostics);
        let template =
            lifted.hir.templates().iter().find(|item| item.name == "Main").expect("Main template");
        let body = lifted.hir.block(template.body).expect("Main body");
        let count = body
            .effects
            .iter()
            .filter_map(|effect| {
                if let Effect::ConstraintAssignment { .. } = effect {
                    Some(())
                } else {
                    None
                }
            })
            .count();
        assert_eq!(count, 3, "{name}: {:?}", body.effects);
    }
}

#[test]
fn mixed_and_parallel_anonymous_tuples_keep_one_output_binding_per_port() {
    for (name, assignments) in
        [("mixed_anonymous_tuple_valid.circom", 3), ("parallel_anonymous_tuple_valid.circom", 2)]
    {
        let lifted = lift_fixture(name);
        assert!(lifted.diagnostics.is_empty(), "{name}: {:?}", lifted.diagnostics);
        assert!(lifted.incomplete.is_empty(), "{name}: {:?}", lifted.incomplete);
        assert_eq!(
            anonymous_output_assignments(&lifted),
            [("first".into(), "left".into()), ("second".into(), "right".into())]
        );
        let template =
            lifted.hir.templates().iter().find(|item| item.name == "Main").expect("Main template");
        let body = lifted.hir.block(template.body).expect("Main body");
        let targets: Vec<_> = body
            .effects
            .iter()
            .filter_map(|effect| {
                if let Effect::ConstraintAssignment { target, .. } = effect {
                    Some(target.terminal)
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(targets.len(), assignments, "{name}: {:?}", body.effects);
    }
}

#[test]
fn genuinely_unknown_assignment_target_still_reports_an_error() {
    let project = load_sources(
        &[fixture("unknown_symbol_invalid.circom")],
        &[],
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    assert!(project.diagnostics.is_empty(), "{:?}", project.diagnostics);
    let lifted = lift_project(&project);
    assert!(
        lifted.diagnostics.iter().any(|diagnostic| diagnostic.code == SemanticCode::UnknownSymbol),
        "{:?}",
        lifted.diagnostics
    );
}

#[test]
fn compiler_valid_reverse_assignments_bind_the_correct_targets() {
    let lifted = lift_conformance_fixture("source_reverse_assignments_valid.circom");
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    assert!(lifted.incomplete.is_empty(), "{:?}", lifted.incomplete);
    let template = lifted.hir.templates().iter().find(|item| item.name == "Main").expect("Main");
    let body = lifted.hir.block(template.body).expect("Main body");
    let assignments: Vec<_> = body
        .effects
        .iter()
        .filter_map(|effect| {
            let (target, value, kind) = match effect {
                Effect::WitnessAssignment { target, value, .. } => (target, value, "witness"),
                Effect::ConstraintAssignment { target, value, .. } => (target, value, "constraint"),
                _ => return None,
            };
            let ExprKind::Access(source) = &lifted.hir.expression(*value)?.kind else {
                return None;
            };
            let target = &lifted.hir.symbol(target.terminal)?.name;
            let source = &lifted.hir.symbol(source.terminal)?.name;
            Some((target.as_str(), source.as_str(), kind))
        })
        .collect();
    assert_eq!(
        assignments,
        [("witness", "value", "witness"), ("constrained", "value", "constraint")]
    );
}

#[test]
fn compiler_valid_named_anonymous_inputs_keep_their_port_mapping() {
    let lifted = lift_conformance_fixture("source_named_anonymous_inputs_valid.circom");
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    assert!(lifted.incomplete.is_empty(), "{:?}", lifted.incomplete);
    let inputs = lifted
        .hir
        .expressions()
        .iter()
        .find_map(|expression| {
            if let ExprKind::AnonymousComponent { inputs, .. } = &expression.kind {
                Some(inputs)
            } else {
                None
            }
        })
        .expect("anonymous call");
    let bindings: Vec<_> = inputs
        .iter()
        .map(|input| {
            assert_eq!(input.operator, InputAssignmentOperator::Constraint);
            let port = lifted
                .hir
                .port(input.resolved_port().expect("resolved named port"))
                .expect("named input port");
            let target = &lifted.hir.symbol(port.symbol).expect("port symbol").name;
            let ExprKind::Access(value) =
                &lifted.hir.expression(input.value).expect("input expression").kind
            else {
                panic!("named input reads a signal")
            };
            let source = &lifted.hir.symbol(value.terminal).expect("input symbol").name;
            (target.as_str(), source.as_str())
        })
        .collect();
    assert_eq!(bindings, [("right", "b"), ("left", "a")]);
}

#[test]
fn compiler_valid_parallel_calls_keep_both_expression_forms() {
    let lifted = lift_conformance_fixture("source_parallel_expressions_valid.circom");
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    assert!(lifted.incomplete.is_empty(), "{:?}", lifted.incomplete);
    let template = lifted.hir.templates().iter().find(|item| item.name == "Main").expect("Main");
    let body = lifted.hir.block(template.body).expect("Main body");
    let mut regular = false;
    let mut anonymous = false;
    for effect in &body.effects {
        let value = match effect {
            Effect::ComponentInstantiation { value, .. }
            | Effect::ConstraintAssignment { value, .. } => *value,
            _ => continue,
        };
        let Some(ExprKind::Parallel(inner)) =
            lifted.hir.expression(value).map(|expression| &expression.kind)
        else {
            continue;
        };
        match &lifted.hir.expression(*inner).expect("parallel operand").kind {
            ExprKind::Call { .. } => regular = true,
            ExprKind::AnonymousComponent { .. } => anonymous = true,
            _ => panic!("parallel expression wraps a template call"),
        }
    }
    assert!(regular && anonymous, "parallel forms must remain typed");
}
