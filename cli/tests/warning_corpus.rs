use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../tests/warnings")
}

fn manifest() -> Vec<Value> {
    let manifest = std::fs::read_to_string(root().join("manifest.json"))
        .expect("failed to read warning corpus manifest");
    let manifest: Value = serde_json::from_str(&manifest).expect("invalid warning corpus manifest");
    assert_eq!(manifest["schema"], 1);
    manifest["cases"].as_array().expect("missing warning cases").clone()
}

fn field<'a>(case: &'a Value, key: &str) -> &'a str {
    case[key].as_str().unwrap_or_else(|| panic!("missing {key} in {case}"))
}

fn source(case: &Value) -> PathBuf {
    let relative = Path::new(field(case, "source"));
    assert!(relative.is_relative());
    for part in relative.components() {
        if let std::path::Component::Normal(_) = part {
            continue;
        }
        panic!("invalid warning corpus path: {}", relative.display());
    }
    let source = root().join(relative);
    assert!(source.is_file(), "missing fixture: {}", source.display());
    source
}

fn count_legacy_findings(case: &Value) -> (usize, bool) {
    let source = source(case);
    let sarif = std::env::temp_dir().join(format!(
        "circomspect-warning-{}-{}.sarif",
        std::process::id(),
        field(case, "id")
    ));
    let curve = if field(case, "curve") == "bls12381" { "BLS12_381" } else { "BN254" };
    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .arg(&source)
        .arg("--curve")
        .arg(curve)
        .arg("--sarif-file")
        .arg(&sarif)
        .output()
        .expect("failed to run Circomspect");
    assert!(sarif.is_file(), "{}: CLI wrote no SARIF: {:?}", field(case, "id"), output);
    let stdout = String::from_utf8(output.stdout).expect("CLI stdout is not UTF-8");
    let analyzed = stdout.contains(&format!("analyzing template '{}'", field(case, "scope")));
    let text = std::fs::read_to_string(&sarif).expect("failed to read SARIF");
    std::fs::remove_file(&sarif).expect("failed to remove SARIF");
    let sarif: Value = serde_json::from_str(&text).expect("invalid CLI SARIF");
    let results = sarif["runs"][0]["results"].as_array().expect("missing SARIF results");
    let count =
        results.iter().filter(|result| result["ruleId"] == field(case, "legacy_rule_id")).count();
    (count, analyzed)
}

fn compiler_class(binary: &Path, case: &Value) -> String {
    let output_dir = std::env::temp_dir().join(format!(
        "circomspect-warning-oracle-{}-{}",
        std::process::id(),
        field(case, "id")
    ));
    std::fs::create_dir_all(&output_dir).expect("failed to create compiler output directory");
    let output = Command::new(binary)
        .arg(source(case))
        .arg("--prime")
        .arg(field(case, "curve"))
        .arg("--no_asm")
        .arg("--output")
        .arg(&output_dir)
        .output()
        .expect("failed to run pinned Circom compiler");
    std::fs::remove_dir_all(output_dir).expect("failed to remove compiler output directory");
    if output.status.success() {
        return "success".to_string();
    }
    let stderr = String::from_utf8(output.stderr).expect("compiler stderr is not UTF-8");
    if stderr.contains("error[P") {
        "syntax_error".to_string()
    } else {
        "semantic_error".to_string()
    }
}

#[test]
fn warning_labels_and_legacy_results_are_frozen() {
    let cases = manifest();
    let mut ids = HashSet::new();
    let mut labels: HashMap<&str, HashSet<&str>> = HashMap::new();
    let mut totals: HashMap<&str, usize> = HashMap::new();
    for case in &cases {
        let id = field(case, "id");
        assert!(ids.insert(id), "duplicate warning case: {id}");
        let rule = field(case, "rule");
        let expected = field(case, "expected");
        labels.entry(rule).or_default().insert(expected);
        assert!(!field(case, "rule_id").is_empty());
        assert!(!field(case, "reason").is_empty());
        let truth = field(case, "truth");
        match expected {
            "emit" => assert_eq!(truth, "confirmed_property"),
            "no_finding" => assert_eq!(truth, "property_absent"),
            "abstain" => assert_eq!(truth, "undetermined"),
            other => panic!("invalid expected outcome: {other}"),
        }
        let (count, analyzed) = count_legacy_findings(case);
        assert_eq!(case["legacy_observed_count"], count, "{id}");
        assert_eq!(case["legacy_analyzed"], analyzed, "{id}");
        let label = match expected {
            "emit" if count > 0 => "TP",
            "emit" => "FN",
            "no_finding" if count > 0 => "FP",
            "no_finding" => "TN",
            "abstain" => "abstention",
            other => panic!("invalid expected outcome: {other}"),
        };
        *totals.entry(label).or_default() += 1;
    }
    assert_eq!(cases.len(), 45);
    assert_eq!(labels.len(), 15);
    assert!(labels.values().all(|set| set.len() == 3));
    assert_eq!(totals.get("TP"), Some(&8));
    assert_eq!(totals.get("FP"), Some(&3));
    assert_eq!(totals.get("FN"), Some(&7));
    assert_eq!(totals.get("TN"), Some(&12));
    assert_eq!(totals.get("abstention"), Some(&15));
}

#[test]
#[ignore = "requires CIRCOM_COMPILER; CI builds and runs the pinned compiler"]
fn warning_cases_have_recorded_compiler_classes() {
    let binary = std::env::var_os("CIRCOM_COMPILER")
        .map(PathBuf::from)
        .expect("set CIRCOM_COMPILER to the pinned Circom 2.2.3 binary");
    for case in manifest() {
        let expected = field(&case, "compiler_class");
        if expected == "no_main" {
            continue;
        }
        let actual = compiler_class(&binary, &case);
        assert_eq!(actual, expected, "{}", field(&case, "id"));
    }
}

#[test]
fn future_diagnostic_contracts_are_explicitly_pending() {
    let contract_root = root().join("../contracts");
    let text = std::fs::read_to_string(contract_root.join("pending.json"))
        .expect("failed to read pending diagnostic contracts");
    let contract: Value = serde_json::from_str(&text).expect("invalid pending contract JSON");
    assert_eq!(contract["status"], "pending_phase_7");
    let cases = contract["cases"].as_array().expect("pending contract cases missing");
    assert_eq!(cases.len(), 6);
    let mut ids = HashSet::new();
    for case in cases {
        let id = field(case, "id");
        assert!(ids.insert(id), "duplicate pending contract: {id}");
        let source = contract_root.join(field(case, "source"));
        assert!(source.is_file(), "pending source does not exist: {id}");
        assert!(!field(case, "source_scope").is_empty());
        assert!(case["args"].is_array(), "missing arguments: {id}");
        let exit = case["expected_exit_code"].as_u64().expect("missing exit code");
        assert!(exit <= 1, "invalid exit code: {id}");
        let rules = case["expected_rule_ids"].as_array().expect("missing rule IDs");
        let levels = case["expected_sarif_levels"].as_object().expect("missing SARIF levels");
        assert_eq!(rules.len(), levels.len(), "level and rule mismatch: {id}");
        for rule in rules {
            let rule = rule.as_str().expect("rule ID must be text");
            assert!(rule == "CS0019" || rule == "CS0020" || rule == "CS0021");
            assert!(levels.contains_key(rule), "SARIF level missing for {rule}");
        }
    }
    assert!(ids.iter().any(|id| id.starts_with("incomplete_library")));
    assert!(ids.iter().any(|id| id.starts_with("redundant_witness")));
}
