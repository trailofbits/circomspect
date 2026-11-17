// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::assert_is_empty,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

fn corpus_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../tests/conformance")
}

fn required_string<'a>(case: &'a Value, key: &str) -> &'a str {
    case[key].as_str().unwrap_or_else(|| panic!("missing {key} in {case}"))
}

fn diagnostic_codes(output: &str) -> Vec<&str> {
    let mut codes = Vec::new();
    for tail in output.split("error[").skip(1) {
        let Some((code, _)) = tail.split_once(']') else {
            continue;
        };
        codes.push(code);
    }
    codes
}

fn analyzer_errors(source: &Path, output_dir: &Path, id: &str) -> Vec<Value> {
    let sarif_path = output_dir.join("analyzer.sarif");
    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .arg(source)
        .args(["--curve", "BN254", "--level", "error", "--timeout", "2"])
        .arg("--sarif-file")
        .arg(&sarif_path)
        .output()
        .expect("failed to run Circomspect on accepted compiler case");
    assert!(
        sarif_path.is_file(),
        "{id}: Circomspect wrote no SARIF; status={}, stdout={}, stderr={}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let sarif: Value = serde_json::from_slice(
        &std::fs::read(&sarif_path).expect("failed to read Circomspect SARIF"),
    )
    .expect("invalid Circomspect SARIF");
    let results = sarif["runs"][0]["results"].as_array().expect("missing SARIF results");
    let errors: Vec<_> =
        results.iter().filter(|result| result["level"] == "error").cloned().collect();
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(!stdout.contains("timed out"), "{id}: Circomspect analysis timed out: {stdout}");
    assert!(output.status.success() || !errors.is_empty(), "{id}: {stdout}");
    errors
}

fn run_case(binary: &Path, case: &Value) {
    let root = corpus_root();
    let relative = Path::new(required_string(case, "source"));
    assert!(relative.is_relative());
    for part in relative.components() {
        if let std::path::Component::Normal(_) = part {
            continue;
        }
        panic!("invalid conformance source path: {}", relative.display());
    }
    let source = root.join(relative);
    assert!(source.is_file(), "missing conformance source: {}", source.display());
    let source = source.canonicalize().expect("canonicalize conformance source");
    let text = std::fs::read_to_string(&source).expect("failed to read conformance source");
    if required_string(case, "expected_syntax") == "accept" {
        let expected_pragma = if required_string(case, "id") == "old_pragma_bus_success" {
            "pragma circom 2.1.0;\n"
        } else {
            "pragma circom 2.2.3;\n"
        };
        assert!(text.starts_with(expected_pragma), "{}", source.display());
    }
    assert_eq!(required_string(case, "curve"), "bn128");
    assert!(required_string(case, "min_version").starts_with("2."));
    let output_dir = std::env::temp_dir().join(format!(
        "circomspect-conformance-{}-{}",
        std::process::id(),
        required_string(case, "id")
    ));
    std::fs::create_dir_all(&output_dir).expect("failed to create compiler output directory");
    let output = Command::new(binary)
        .arg(&source)
        .arg("--no_asm")
        .arg("--prime")
        .arg(required_string(case, "curve"))
        .arg("--output")
        .arg(&output_dir)
        .output()
        .expect("failed to run pinned Circom compiler");
    let stderr = String::from_utf8(output.stderr).expect("compiler stderr is not UTF-8");
    let codes = diagnostic_codes(&stderr);
    let expected = required_string(case, "compiler_class");
    let class = if output.status.success() {
        "success"
    } else if stderr.contains("panicked at") && codes.is_empty() {
        "compiler_panic"
    } else if codes == ["P1001"] {
        "project_error"
    } else if codes.iter().any(|code| code.starts_with('P')) {
        "syntax_error"
    } else {
        "semantic_error"
    };
    assert_eq!(class, expected, "{}: {stderr}", required_string(case, "id"));
    let code = required_string(case, "compiler_code");
    let syntax = match class {
        "syntax_error" => "reject",
        "compiler_panic" => "indeterminate",
        "success" | "semantic_error" | "project_error" => "accept",
        other => panic!("unexpected compiler class: {other}"),
    };
    assert_eq!(required_string(case, "expected_syntax"), syntax, "{}", required_string(case, "id"));
    assert_eq!(
        codes.first().copied().unwrap_or(""),
        code,
        "{}: {stderr}",
        required_string(case, "id")
    );
    if class == "syntax_error" {
        assert!(code.starts_with('P'), "{}: {stderr}", required_string(case, "id"));
    }
    if class == "success" {
        let errors = analyzer_errors(&source, &output_dir, required_string(case, "id"));
        assert!(
            errors.is_empty(),
            "{}: compiler accepted {}, Circomspect source errors: {errors:#?}",
            required_string(case, "id"),
            source.display()
        );
    }
    if let Some(expected_code) = case["analyzer_code"].as_str() {
        let errors = analyzer_errors(&source, &output_dir, required_string(case, "id"));
        assert!(
            errors.iter().any(|result| result["ruleId"] == expected_code),
            "{}: Circomspect did not preserve {expected_code}: {errors:#?}",
            required_string(case, "id")
        );
    }
    std::fs::remove_dir_all(output_dir).expect("failed to remove compiler output directory");
}

#[test]
fn production_matrix_has_existing_cases_and_valid_spans() {
    let root = corpus_root();
    let manifest: Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("manifest.json")).expect("missing manifest"),
    )
    .expect("invalid manifest");
    let cases = manifest["cases"].as_array().expect("missing cases");
    let cases: HashMap<_, _> =
        cases.iter().map(|case| (required_string(case, "id"), case)).collect();
    let matrix: Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("production_matrix.json"))
            .expect("missing production matrix"),
    )
    .expect("invalid production matrix");
    assert_eq!(matrix["compiler_commit"], manifest["compiler_commit"]);
    let rows = matrix["rows"].as_array().expect("missing matrix rows");
    assert!(!rows.is_empty());
    let inventory: Value = serde_json::from_str(
        &std::fs::read_to_string(root.join("grammar_inventory.json"))
            .expect("missing independent grammar inventory"),
    )
    .expect("invalid grammar inventory");
    assert_eq!(inventory["compiler_commit"], manifest["compiler_commit"]);
    let expected_ids = inventory["row_ids"].as_array().expect("missing inventory IDs");
    let expected_count = expected_ids.len();
    let expected_ids: HashSet<_> =
        expected_ids.iter().map(|value| value.as_str().expect("nonstring ID")).collect();
    assert_eq!(expected_ids.len(), expected_count);
    let mut ids = HashSet::new();
    for row in rows {
        let id = required_string(row, "id");
        assert!(ids.insert(id), "duplicate production ID: {id}");
        assert!(!required_string(row, "grammar").is_empty());
        assert!(required_string(row, "min_version").starts_with("2."));
        let expectation = &row["ast_expectation"];
        let kind = required_string(expectation, "kind");
        for key in ["operator", "modifier", "direction", "initializer", "shape"] {
            if let Some(value) = expectation.get(key) {
                assert!(!value.as_str().unwrap_or("").is_empty(), "{id}: invalid {key}");
            }
        }
        if ["binary", "unary", "assignment", "postfix_update"].contains(&kind) {
            required_string(expectation, "operator");
        }
        if id.starts_with("precedence_")
            || id.starts_with("associativity_")
            || id == "ternary_arm_boundary"
            || id == "dangling_else"
            || id == "nested_if_no_else"
            || id == "top_level_order"
        {
            required_string(expectation, "shape");
        }
        let accepted = cases
            .get(required_string(row, "accept_case"))
            .unwrap_or_else(|| panic!("{id}: missing accepted case"));
        assert_eq!(required_string(accepted, "expected_syntax"), "accept", "{id}");
        assert_eq!(
            required_string(accepted, "min_version"),
            required_string(row, "min_version"),
            "{id}"
        );
        let rejected = cases
            .get(required_string(row, "reject_case"))
            .unwrap_or_else(|| panic!("{id}: missing rejected case"));
        assert_eq!(required_string(rejected, "compiler_class"), "syntax_error", "{id}");
        assert_eq!(
            required_string(rejected, "min_version"),
            required_string(row, "min_version"),
            "{id}"
        );
        let source = root.join(required_string(accepted, "source"));
        let text = std::fs::read_to_string(source).expect("missing accepted source");
        let start = usize::try_from(row["span"]["start"].as_u64().expect("missing span start"))
            .expect("span start exceeds usize");
        let end = usize::try_from(row["span"]["end"].as_u64().expect("missing span end"))
            .expect("span end exceeds usize");
        assert!(start < end && text.is_char_boundary(start) && text.is_char_boundary(end));
        let focal_start = match required_string(row, "focal_kind") {
            "expr" => text.rfind("out <== ").expect("expression wrapper missing") + 8,
            "stmt" => text.find("var x=1;\n").expect("statement wrapper missing") + 9,
            "decl" => text.find("template Main(){\n").expect("declaration wrapper missing") + 17,
            "function" => text.find("function F(x){\n").expect("function wrapper missing") + 15,
            "top" | "existing" => 0,
            other => panic!("unknown focal kind: {other}"),
        };
        assert!(start >= focal_start, "{id}: span points outside the focal construct");
        assert_eq!(&text[start..end], required_string(&row["span"], "text"), "{id}");
        let rejected_text = std::fs::read_to_string(root.join(required_string(rejected, "source")))
            .expect("missing malformed source");
        assert_ne!(text, rejected_text, "{id}: malformed fixture equals accepted fixture");
    }
    assert_eq!(ids, expected_ids, "matrix differs from pinned grammar inventory");
}

fn terminal_tokens(grammar: &str, start: &str, end: &str) -> HashSet<String> {
    let (_, tail) = grammar.split_once(start).expect("upstream grammar section missing");
    let (section, _) = tail.split_once(end).expect("upstream grammar section end missing");
    let mut tokens = HashSet::new();
    for line in section.lines() {
        let line = line.trim();
        if !line.starts_with('"') {
            continue;
        }
        let Some((literal, _)) = line.split_once("=>") else {
            continue;
        };
        let token: String = serde_json::from_str(literal.trim())
            .expect("invalid quoted operator in pinned grammar");
        tokens.insert(token);
    }
    tokens
}

fn check_pinned_grammar(binary: &Path, rows: &[Value]) {
    let source_root = binary
        .parent()
        .and_then(Path::parent)
        .and_then(Path::parent)
        .expect("compiler binary must be under target/release");
    let grammar = std::fs::read_to_string(source_root.join("parser/src/lang.lalrpop"))
        .expect("pinned compiler grammar is missing");
    let operators = terminal_tokens(&grammar, "ParseExpressionPrefixOpcode:", "ParseAssignOp:");
    let assignments = terminal_tokens(&grammar, "ParseAssignOp:", "DECNUMBER:");
    let mut covered_operators = HashSet::new();
    let mut covered_assignments = HashSet::new();
    for row in rows {
        let reference = required_string(row, "grammar");
        let (production, variant) = reference.split_once('#').expect("missing grammar variant");
        match production {
            "ExpressionOp" | "ParseExpressionPrefixOpcode" => {
                covered_operators.insert(variant.to_owned());
            }
            "ParseAssignOp" => {
                covered_assignments.insert(variant.to_owned());
            }
            "Lexer" | "Precedence" => {}
            _ => assert!(grammar.contains(production), "unknown upstream production: {reference}"),
        }
    }
    assert_eq!(covered_operators, operators, "expression operator inventory differs from grammar");
    assert_eq!(
        covered_assignments, assignments,
        "assignment operator inventory differs from grammar"
    );
    assert!(grammar.contains("<main:ParseMainComponent?>"));
    assert!(grammar.contains("<arg_names: ParseParenthesisArguments?>"));
}

#[test]
#[ignore = "requires CIRCOM_COMPILER; CI builds and runs the pinned compiler"]
fn official_circom_223_syntax_corpus() {
    let binary = std::env::var_os("CIRCOM_COMPILER")
        .map(PathBuf::from)
        .expect("set CIRCOM_COMPILER to the pinned Circom 2.2.3 binary");
    let version = Command::new(&binary)
        .arg("--version")
        .output()
        .expect("failed to query Circom compiler version");
    assert!(version.status.success(), "Circom --version failed");
    let version = String::from_utf8(version.stdout).expect("compiler version is not UTF-8");
    assert_eq!(version.trim(), "circom compiler 2.2.3");
    let manifest = std::fs::read_to_string(corpus_root().join("manifest.json"))
        .expect("failed to read conformance manifest");
    let manifest: Value = serde_json::from_str(&manifest).expect("invalid conformance manifest");
    assert_eq!(manifest["compiler_version"], "2.2.3");
    assert_eq!(manifest["compiler_commit"], "ad44e915a12bb047b05745c2884aad9cc8326bc6");
    let cases = manifest["cases"].as_array().expect("conformance cases are missing");
    assert!(!cases.is_empty(), "conformance corpus is empty");
    let matrix: Value = serde_json::from_str(
        &std::fs::read_to_string(corpus_root().join("production_matrix.json"))
            .expect("missing production matrix"),
    )
    .expect("invalid production matrix");
    check_pinned_grammar(&binary, matrix["rows"].as_array().expect("missing matrix rows"));
    let mut ids = HashSet::new();
    let mut pairs: HashMap<&str, (bool, bool)> = HashMap::new();
    for case in cases {
        let id = required_string(case, "id");
        assert!(ids.insert(id), "duplicate case ID: {id}");
        let feature = required_string(case, "feature");
        if feature != "semantic_control" && feature != "compiler_boundary" {
            let pair = pairs.entry(feature).or_default();
            match required_string(case, "expected_syntax") {
                "accept" => pair.0 = true,
                "reject" => pair.1 = true,
                other => panic!("invalid syntax expectation: {other}"),
            }
        }
        run_case(&binary, case);
    }
    assert!(pairs.len() >= 18, "baseline feature inventory shrank");
    assert!(pairs.values().all(|pair| pair.0 && pair.1));
}
