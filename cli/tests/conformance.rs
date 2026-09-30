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
    let text = std::fs::read_to_string(&source).expect("failed to read conformance source");
    assert!(text.starts_with("pragma circom 2.2.3;\n"), "{}", source.display());
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
    } else if codes.iter().any(|code| code.starts_with('P')) {
        "syntax_error"
    } else {
        "semantic_error"
    };
    assert_eq!(class, expected, "{}: {stderr}", required_string(case, "id"));
    let code = required_string(case, "compiler_code");
    assert_eq!(
        required_string(case, "expected_syntax"),
        if class == "syntax_error" { "reject" } else { "accept" },
        "{}",
        required_string(case, "id")
    );
    assert_eq!(
        codes.first().copied().unwrap_or(""),
        code,
        "{}: {stderr}",
        required_string(case, "id")
    );
    if class == "syntax_error" {
        assert!(code.starts_with('P'), "{}: {stderr}", required_string(case, "id"));
    }
    std::fs::remove_dir_all(output_dir).expect("failed to remove compiler output directory");
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
    let mut ids = HashSet::new();
    let mut pairs: HashMap<&str, (bool, bool)> = HashMap::new();
    for case in cases {
        let id = required_string(case, "id");
        assert!(ids.insert(id), "duplicate case ID: {id}");
        let feature = required_string(case, "feature");
        if feature != "semantic_control" {
            let pair = pairs.entry(feature).or_default();
            match required_string(case, "expected_syntax") {
                "accept" => pair.0 = true,
                "reject" => pair.1 = true,
                other => panic!("invalid syntax expectation: {other}"),
            }
        }
        run_case(&binary, case);
    }
    assert_eq!(pairs.len(), 18, "feature inventory changed without review");
    assert!(pairs.values().all(|pair| pair.0 && pair.1));
}
