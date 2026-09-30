use circomspect_parser::new_frontend::{
    parse_source, SourceId, SyntaxCategory, Version, VersionPolicy, WalkSyntax,
};
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
        let start = row["span"]["start"].as_u64().expect("span start") as usize;
        let end = row["span"]["end"].as_u64().expect("span end") as usize;
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
    assert!(matrix_assertions::assert_expectation(&ast, &wrong_operator, focal..focal + 1).is_err());
    let wrong_shape = serde_json::json!({
        "kind": "binary",
        "operator": "add",
        "shape": "multiply(add(1,2),3)"
    });
    assert!(matrix_assertions::assert_expectation(&ast, &wrong_shape, focal..focal + 1).is_err());
}
