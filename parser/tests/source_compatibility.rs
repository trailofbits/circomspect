// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(clippy::allow_attributes, clippy::assert_is_empty, clippy::expect_used, clippy::panic)]

use circomspect_parser::frontend::{
    load_sources, parse_source, tokenize, DiagnosticKind, SourceId, TriviaKind, Version,
    VersionPolicy,
};
use circomspect_parser::hir::{lift_project, Effect, SemanticCode};
use circomspect_parser::frontend::AssignmentOperator;
use std::path::PathBuf;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/source_compatibility").join(name)
}

fn parse_fixture(name: &str) -> circomspect_parser::frontend::ParseOutcome {
    let text = std::fs::read_to_string(fixture(name)).expect("fixture is readable");
    parse_source(SourceId::new(0), &text, VersionPolicy::new(Version::new(2, 2, 3)))
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
