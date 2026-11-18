// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use circomspect_parser::frontend::{
    load_sources, parse_source, DiagnosticKind, SourceId, SyntaxCategory, Version, VersionPolicy,
    WalkSyntax,
};
use circomspect_parser::hir::{lift_project, Effect, IncompleteReason};
use serde_json::Value;
use std::collections::HashMap;
use std::path::PathBuf;

#[path = "support/matrix_assertions.rs"]
mod matrix_assertions;

fn corpus_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../tests/conformance")
}

fn required<'a>(value: &'a Value, key: &str) -> &'a str {
    value[key].as_str().unwrap_or_else(|| panic!("missing {key}: {value}"))
}

fn case_source(case: &Value) -> String {
    let path = corpus_root().join(required(case, "source"));
    std::fs::read_to_string(path).expect("corpus source file")
}

fn focal_category(kind: &str) -> SyntaxCategory {
    match kind {
        "top" => SyntaxCategory::Item,
        "function" => SyntaxCategory::Definition,
        "stmt" => SyntaxCategory::Statement,
        "decl" => SyntaxCategory::Declaration,
        "expr" | "existing" => SyntaxCategory::Expression,
        other => panic!("unknown focal kind: {other}"),
    }
}

#[test]
fn owned_parser_agrees_with_pinned_compiler_syntax_matrix() {
    let root = corpus_root();
    let manifest: Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("manifest.json")).expect("manifest"),
    )
    .expect("valid manifest");
    let cases: HashMap<_, _> = manifest["cases"]
        .as_array()
        .expect("cases")
        .iter()
        .map(|case| (required(case, "id"), case))
        .collect();
    let matrix: Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("production_matrix.json")).expect("matrix"),
    )
    .expect("valid matrix");
    let mut failures = Vec::new();
    for row in matrix["rows"].as_array().expect("rows") {
        let id = required(row, "id");
        let accepted = cases.get(required(row, "accept_case")).expect("accepted case");
        let rejected = cases.get(required(row, "reject_case")).expect("rejected case");
        let source = case_source(accepted);
        let outcome =
            parse_source(SourceId::new(0), &source, VersionPolicy::new(Version::new(2, 2, 3)));
        if !outcome.diagnostics.is_empty() {
            failures.push(format!("{id}: accepted source rejected: {:?}", outcome.diagnostics));
        }
        let start = usize::try_from(row["span"]["start"].as_u64().expect("span start"))
            .expect("span fits usize");
        let end = usize::try_from(row["span"]["end"].as_u64().expect("span end"))
            .expect("span fits usize");
        let category = if id == "comment_line" || id == "comment_block" {
            SyntaxCategory::Trivia
        } else {
            focal_category(required(row, "focal_kind"))
        };
        let mut found = false;
        outcome.ast.walk_syntax(None, &mut |kind, span, _| {
            if kind == category && span.start() <= start && span.end() >= end {
                found = true;
            }
        });
        if !found {
            failures.push(format!("{id}: no {category:?} AST node covers {start}..{end}"));
        }
        if let Err(error) =
            matrix_assertions::assert_expectation(&outcome.ast, &row["ast_expectation"], start..end)
        {
            failures.push(format!("{id}: {error}"));
        }
        let source = case_source(rejected);
        let rejected =
            parse_source(SourceId::new(0), &source, VersionPolicy::new(Version::new(2, 2, 3)));
        if rejected.diagnostics.is_empty() {
            failures.push(format!("{id}: rejected source accepted"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} parser disagreements:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn typed_expectations_reject_wrong_operator_and_precedence() {
    let source = "function F() { return 1 + 2 * 3; }";
    let ast = parse_source(SourceId::new(0), source, VersionPolicy::new(Version::new(2, 2, 3))).ast;
    let focal = source.find('+').expect("addition operator");
    let wrong_operator = serde_json::json!({"kind": "binary", "operator": "subtract"});
    let operator_result =
        matrix_assertions::assert_expectation(&ast, &wrong_operator, focal..focal + 1);
    assert!(operator_result.is_err());
    let wrong_shape = serde_json::json!({
        "kind": "binary",
        "operator": "add",
        "shape": "multiply(add(1,2),3)"
    });
    assert!(matrix_assertions::assert_expectation(&ast, &wrong_shape, focal..focal + 1).is_err());
}

#[test]
fn owned_parser_agrees_with_every_determinate_compiler_case() {
    let root = corpus_root();
    let manifest: Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("manifest.json")).expect("manifest"),
    )
    .expect("valid manifest");
    let mut failures = Vec::new();
    for case in manifest["cases"].as_array().expect("cases") {
        let expected = required(case, "expected_syntax");
        if expected == "indeterminate" {
            continue;
        }
        let source = case_source(case);
        let outcome =
            parse_source(SourceId::new(0), &source, VersionPolicy::new(Version::new(2, 2, 3)));
        let accepted = outcome.diagnostics.is_empty();
        if (expected == "accept") != accepted {
            failures.push(format!(
                "{}: expected {expected}, diagnostics {:?}",
                required(case, "id"),
                outcome.diagnostics
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "{} syntax disagreements:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn compiler_success_cases_have_supported_hir_forms() {
    let root = corpus_root();
    let manifest: Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("manifest.json")).expect("manifest"),
    )
    .expect("valid manifest");
    let mut unsupported = Vec::new();
    for case in manifest["cases"].as_array().expect("cases") {
        if required(case, "compiler_class") != "success" {
            continue;
        }
        let path = root.join(required(case, "source"));
        let loaded = load_sources(&[path], &[], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        for region in &lifted.incomplete {
            if let IncompleteReason::Unsupported(reason) = &region.reason {
                unsupported.push(format!("{}: {reason}", required(case, "id")));
            }
        }
        for block in lifted.hir.blocks() {
            for effect in &block.effects {
                let (Effect::Opaque { reason, .. }
                | Effect::OpaqueAssignment { reason, .. }
                | Effect::OpaqueEquality { reason, .. }) = effect
                else {
                    continue;
                };
                if let IncompleteReason::Unsupported(_)
                | IncompleteReason::InvalidAssignment
                | IncompleteReason::Syntax = reason
                {
                    unsupported.push(format!("{}: opaque effect {reason:?}", required(case, "id")));
                }
            }
        }
    }
    assert!(unsupported.is_empty(), "compiler-success HIR gaps:\n{}", unsupported.join("\n"));
}

fn predecessor(version: &str) -> Option<Version> {
    match version {
        "2.0.6" => Some(Version::new(2, 0, 5)),
        "2.0.7" => Some(Version::new(2, 0, 6)),
        "2.0.8" => Some(Version::new(2, 0, 7)),
        "2.1.0" => Some(Version::new(2, 0, 8)),
        "2.1.1" => Some(Version::new(2, 1, 0)),
        "2.2.0" => Some(Version::new(2, 1, 1)),
        "2.2.3" => Some(Version::new(2, 2, 2)),
        "2.0.0" => None,
        other => panic!("unreviewed Circom release in matrix: {other}"),
    }
}

fn corpus_version(version: &str) -> Version {
    let mut parts = version.split('.');
    let major = parts.next().expect("major version").parse().expect("numeric major version");
    let minor = parts.next().expect("minor version").parse().expect("numeric minor version");
    let patch = parts.next().expect("patch version").parse().expect("numeric patch version");
    assert!(parts.next().is_none(), "too many version components");
    Version::new(major, minor, patch)
}

#[test]
fn matrix_features_enforce_target_version_without_locking_to_source_pragma() {
    let root = corpus_root();
    let manifest: Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("manifest.json")).expect("manifest"),
    )
    .expect("valid manifest");
    let cases: HashMap<_, _> = manifest["cases"]
        .as_array()
        .expect("cases")
        .iter()
        .map(|case| (required(case, "id"), case))
        .collect();
    let matrix: Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("production_matrix.json")).expect("matrix"),
    )
    .expect("valid matrix");
    let mut failures = Vec::new();
    for row in matrix["rows"].as_array().expect("rows") {
        let Some(target) = predecessor(required(row, "min_version")) else {
            continue;
        };
        let id = required(row, "id");
        let case = cases.get(required(row, "accept_case")).expect("accepted case");
        let accepted_source = case_source(case);
        let source = accepted_source.replacen(
            "pragma circom 2.2.3;",
            &format!("pragma circom {}.{}.{};", target.major, target.minor, target.patch),
            1,
        );
        let outcome = parse_source(SourceId::new(0), &source, VersionPolicy::new(target));
        let focal_start = usize::try_from(row["span"]["start"].as_u64().expect("focal start"))
            .expect("span fits usize");
        let focal_end = usize::try_from(row["span"]["end"].as_u64().expect("focal end"))
            .expect("span fits usize");
        let mut declaration = None;
        outcome.ast.walk_syntax(None, &mut |category, span, _| {
            if category == SyntaxCategory::Declaration
                && span.start() <= focal_start
                && span.end() >= focal_end
            {
                declaration = Some(span);
            }
        });
        let definite = outcome.diagnostics.iter().any(|diagnostic| {
            diagnostic.kind == DiagnosticKind::FeatureVersion
                && diagnostic.span().is_some_and(|span| {
                    let focal_hit = span.start() < focal_end && span.end() > focal_start;
                    let bus_header = required(&row["ast_expectation"], "kind") == "bus_declaration"
                        && declaration.is_some_and(|parent| {
                            parent.start() <= span.start() && parent.end() >= span.end()
                        });
                    focal_hit || bus_header
                })
        });
        if id == "inline_array_buses" {
            let pending = outcome.pending_feature_checks.iter().any(|check| {
                check.span.start() <= focal_start
                    && check.span.end() >= focal_end
                    && check.required_version == Version::new(2, 2, 3)
            });
            if definite || !pending {
                failures.push(format!("{id}: expected pending bus type check only"));
            }
        } else if !definite {
            failures.push(format!("{id}: no feature-version diagnostic at {target:?}"));
        }
        let minimum = corpus_version(required(row, "min_version"));
        let minimum_source = accepted_source.replacen(
            "pragma circom 2.2.3;",
            &format!("pragma circom {}.{}.{};", minimum.major, minimum.minor, minimum.patch),
            1,
        );
        let minimum_outcome =
            parse_source(SourceId::new(0), &minimum_source, VersionPolicy::new(minimum));
        if minimum_outcome.diagnostics.iter().any(|diagnostic| {
            diagnostic.kind == DiagnosticKind::FeatureVersion
                && diagnostic
                    .span()
                    .is_some_and(|span| span.start() < focal_end && span.end() > focal_start)
        }) {
            failures.push(format!("{id}: feature rejected at its declared minimum {minimum:?}"));
        }
        if id == "inline_array_buses"
            && minimum_outcome
                .pending_feature_checks
                .iter()
                .any(|check| check.span.start() <= focal_start && check.span.end() >= focal_end)
        {
            failures.push(format!("{id}: bus-array check remains pending at {minimum:?}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} version disagreements:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
