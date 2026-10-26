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
use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use program_analysis::new_rules::RuleKind;
use serde_json::{json, Value};

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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ScopeKind {
    Definition,
    SourceRecovery,
}

impl ScopeKind {
    fn name(self) -> &'static str {
        match self {
            Self::Definition => "definition",
            Self::SourceRecovery => "source_recovery",
        }
    }
}

struct ObservedEvidence {
    scope_kind: ScopeKind,
    syntax_error: bool,
    findings: Vec<Value>,
    analyzed: bool,
    incomplete: bool,
    incomplete_scopes: Vec<Value>,
    target_code_incomplete_scopes: usize,
    seconds: f64,
    exit_code: Option<i32>,
}

fn observed_evidence(case: &Value) -> ObservedEvidence {
    let source = source(case);
    let canonical_source = source.canonicalize().expect("failed to canonicalize warning fixture");
    let expected_uri = url::Url::from_file_path(&canonical_source).unwrap().to_string();
    let (scope_start, scope_end, scope_kind) = scope_lines(case, &source);
    let sarif = std::env::temp_dir().join(format!(
        "circomspect-warning-{}-{}.sarif",
        std::process::id(),
        field(case, "id")
    ));
    let curve = if field(case, "curve") == "bls12381" { "BLS12_381" } else { "BN254" };
    let start = Instant::now();
    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .arg(&source)
        .arg("--curve")
        .arg(curve)
        .args(["--level", "info"])
        .arg("--sarif-file")
        .arg(&sarif)
        .output()
        .expect("failed to run Circomspect");
    let seconds = start.elapsed().as_secs_f64();
    assert!(sarif.is_file(), "{}: CLI wrote no SARIF: {:?}", field(case, "id"), output);
    let stdout = String::from_utf8(output.stdout).expect("CLI stdout is not UTF-8");
    let analyzed = stdout.contains(&format!("analyzing template '{}'", field(case, "scope")));
    let text = std::fs::read_to_string(&sarif).expect("failed to read SARIF");
    std::fs::remove_file(&sarif).expect("failed to remove SARIF");
    let sarif: Value = serde_json::from_str(&text).expect("invalid CLI SARIF");
    let results = sarif["runs"][0]["results"].as_array().expect("missing SARIF results");
    let mut evidence = Vec::new();
    let mut syntax_error = false;
    let mut incomplete = false;
    let mut incomplete_scopes = Vec::new();
    let mut target_code_incomplete_scopes = 0;
    for result in results {
        let physical = &result["locations"][0]["physicalLocation"];
        let line = physical["region"]["startLine"].as_u64().expect("located diagnostic");
        if physical["artifactLocation"]["uri"] != expected_uri
            || line < scope_start
            || line > scope_end
        {
            continue;
        }
        if result["ruleId"] == "P1000" && result["level"] == "error" {
            syntax_error = true;
        }
        if result["ruleId"] == "CS0020" {
            incomplete = true;
            if incomplete_names_code(result, field(case, "rule_id")) {
                target_code_incomplete_scopes += 1;
            }
            incomplete_scopes.push(result.clone());
        }
        if result["ruleId"] != field(case, "rule_id") {
            continue;
        }
        let message = result["message"]["text"].as_str().expect("finding message is missing");
        let locations = result["locations"].as_array().expect("finding locations are missing");
        assert!(locations.len() <= 1, "finding has multiple primary locations");
        let span = if let Some(location) = locations.first() {
            let physical = &location["physicalLocation"];
            assert_eq!(physical["artifactLocation"]["uri"], expected_uri);
            let region = &physical["region"];
            json!({
                "startLine": region["startLine"],
                "startColumn": region["startColumn"],
                "endLine": region["endLine"],
                "endColumn": region["endColumn"],
            })
        } else {
            assert!(message.contains(field(case, "scope")), "locationless finding lacks scope");
            Value::Null
        };
        evidence.push(json!({ "message": message, "span": span }));
    }
    evidence.sort_by_key(Value::to_string);
    ObservedEvidence {
        scope_kind,
        syntax_error,
        findings: evidence,
        analyzed,
        incomplete,
        incomplete_scopes,
        target_code_incomplete_scopes,
        seconds,
        exit_code: output.status.code(),
    }
}

fn incomplete_names_code(result: &Value, code: &str) -> bool {
    let Some(locations) = result["relatedLocations"].as_array() else { return false };
    locations.iter().any(|location| {
        let Some(message) = location["message"]["text"].as_str() else { return false };
        let Some((codes, _)) = message.split_once(':') else { return false };
        codes.split(',').any(|item| item.trim() == code)
    })
}

fn scope_lines(case: &Value, path: &Path) -> (u64, u64, ScopeKind) {
    use parser::hir::{lift_project, DefinitionRef, IncompleteReason};
    use parser::frontend::{load_sources, Version, VersionPolicy};
    let loaded = load_sources(&[path.to_owned()], &[], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    let (span, kind) = if let Some(definition) = lifted.hir.definition(field(case, "scope")) {
        let span = match definition {
            DefinitionRef::Function(id) => lifted.hir.function(id).unwrap().span,
            DefinitionRef::Template(id) => lifted.hir.template(id).unwrap().span,
            DefinitionRef::Bus(id) => lifted.hir.bus(id).unwrap().span,
        };
        (span, ScopeKind::Definition)
    } else {
        assert_eq!(field(case, "expected"), "abstain", "missing declared corpus scope");
        assert_eq!(field(case, "compiler_class"), "syntax_error");
        let regions: Vec<_> = lifted
            .incomplete
            .iter()
            .filter(|region| region.reason == IncompleteReason::Syntax)
            .collect();
        assert_eq!(regions.len(), 1, "a malformed corpus scope needs one exact syntax region");
        (regions[0].span().expect("source-located syntax recovery"), ScopeKind::SourceRecovery)
    };
    let source = loaded.files.iter().find(|file| file.id == span.source()).unwrap();
    let line =
        |offset| source.text[..offset].bytes().filter(|byte| *byte == b'\n').count() as u64 + 1;
    (line(span.start()), line(span.end()), kind)
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
fn corpus_target_ids_match_the_frozen_rule_contract() {
    let kinds = HashMap::from([
        ("bitwise_complement", RuleKind::BitwiseComplement),
        ("bn254_specific", RuleKind::Bn254SpecificCircuit),
        ("complexity", RuleKind::Complexity),
        ("constant_conditional", RuleKind::ConstantConditional),
        ("field_arithmetic", RuleKind::FieldArithmetic),
        ("field_comparison", RuleKind::FieldComparison),
        ("nonstrict_conversion", RuleKind::NonstrictBinaryConversion),
        ("redundant_witness", RuleKind::RedundantWitnessAssignment),
        ("side_effect_free_assignment", RuleKind::SideEffectFreeAssignment),
        ("signal_assignment", RuleKind::SignalAssignment),
        ("too_many_arguments", RuleKind::TooManyArguments),
        ("unconstrained_division", RuleKind::UnconstrainedDivision),
        ("unconstrained_less_than", RuleKind::UnconstrainedLessThan),
        ("underconstrained_signal", RuleKind::UnconstrainedSignal),
        ("unused_output", RuleKind::UnusedOutputSignal),
    ]);
    for case in manifest() {
        let kind = kinds.get(field(&case, "rule")).expect("corpus rule has a frozen contract");
        assert_eq!(field(&case, "rule_id"), kind.code().id(), "{}", field(&case, "id"));
    }
}

#[test]
fn warning_labels_and_recorded_legacy_results_are_frozen() {
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
        let count = case["legacy_observed_count"].as_u64().expect("legacy count");
        let evidence = case["legacy_observed_evidence"].as_array().expect("legacy evidence");
        assert_eq!(evidence.len() as u64, count, "{id}");
        assert!(case["legacy_analyzed"].is_boolean(), "{id}");
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
    assert_eq!(cases.len(), 48);
    assert_eq!(labels.len(), 15);
    assert!(labels.values().all(|set| set.len() == 3));
    assert_eq!(totals.get("TP"), Some(&8));
    assert_eq!(totals.get("FP"), Some(&2));
    assert_eq!(totals.get("FN"), Some(&7));
    assert_eq!(totals.get("TN"), Some(&16));
    assert_eq!(totals.get("abstention"), Some(&15));
}

#[test]
fn cli_warning_corpus_preserves_adjudicated_findings() {
    run_corpus(manifest());
}

#[test]
#[ignore = "focused evidence run; the full warning corpus also covers these fixtures"]
fn original_conversion_triplet_preserves_cli_evidence() {
    let cases = manifest()
        .into_iter()
        .filter(|case| field(case, "id").starts_with("nonstrict_conversion_"))
        .collect::<Vec<_>>();
    assert_eq!(cases.len(), 3);
    run_corpus(cases);
}

fn run_corpus(cases: Vec<Value>) {
    let mut failures = Vec::new();
    let mut totals = BTreeMap::new();
    let mut observations = Vec::new();
    write_corpus_report(&observations, &totals, &failures, false);
    for case in cases {
        let observed = observed_evidence(&case);
        let expected = field(&case, "expected");
        let label = match (expected, observed.findings.is_empty()) {
            ("emit", false) => "TP",
            ("emit", true) => "FN",
            ("no_finding", false) => "FP",
            ("no_finding", true) => "TN",
            ("abstain", true) => "abstention",
            ("abstain", false) => "unexpected finding",
            (other, _) => panic!("invalid expectation {other}"),
        };
        *totals.entry(label).or_insert(0) += 1;
        let scope_checked = match observed.scope_kind {
            ScopeKind::Definition => observed.analyzed,
            ScopeKind::SourceRecovery => !observed.analyzed && observed.syntax_error,
        };
        if !scope_checked
            || (expected == "abstain" && !has_expected_abstention(&observed))
            || label == "FN"
            || label == "FP"
            || label == "unexpected finding"
        {
            failures.push(format!(
                "{}: {label}, scope analyzed={analyzed}, incomplete={incomplete}, \
                 target incomplete scopes={target_incomplete}",
                field(&case, "id"),
                analyzed = observed.analyzed,
                incomplete = observed.incomplete,
                target_incomplete = observed.target_code_incomplete_scopes,
            ));
        }
        observations.push(json!({
            "id": field(&case, "id"), "rule": field(&case, "rule"),
            "rule_id": field(&case, "rule_id"), "scope": field(&case, "scope"),
            "expected": expected, "classification": label, "analyzed": observed.analyzed,
            "scope_kind": observed.scope_kind.name(), "syntax_error": observed.syntax_error,
            "incomplete": observed.incomplete, "exit_code": observed.exit_code,
            "incomplete_scope_count": observed.incomplete_scopes.len(),
            "target_code_incomplete_scope_count": observed.target_code_incomplete_scopes,
            "incomplete_scopes": observed.incomplete_scopes,
            "seconds": observed.seconds, "findings": observed.findings,
        }));
        write_corpus_report(&observations, &totals, &failures, false);
    }
    write_corpus_report(&observations, &totals, &failures, true);
    assert!(failures.is_empty(), "{totals:?}\n{}", failures.join("\n"));
}

fn has_expected_abstention(observed: &ObservedEvidence) -> bool {
    observed.incomplete
        && match observed.scope_kind {
            ScopeKind::Definition => observed.target_code_incomplete_scopes > 0,
            ScopeKind::SourceRecovery => observed.syntax_error,
        }
}

#[test]
fn unrelated_incompleteness_does_not_satisfy_an_abstention_case() {
    let mut case = manifest()
        .into_iter()
        .find(|case| field(case, "id") == "field_arithmetic_abstain")
        .expect("the arithmetic abstention fixture exists");
    case["rule_id"] = json!("CS0012");
    let observed = observed_evidence(&case);
    assert!(observed.incomplete, "the fixture exercises an unrelated incomplete rule");
    assert_eq!(observed.target_code_incomplete_scopes, 0);
    assert!(!has_expected_abstention(&observed));
}

fn write_corpus_report(
    observations: &[Value],
    totals: &BTreeMap<&str, usize>,
    failures: &[String],
    complete: bool,
) {
    let Some(path) = std::env::var_os("CIRCOMSPECT_CORPUS_REPORT") else { return };
    let report = json!({
        "schema": 1, "complete": complete, "cases": observations,
        "totals": totals, "failures": failures,
    });
    std::fs::write(path, serde_json::to_vec_pretty(&report).unwrap())
        .expect("failed to write warning corpus evidence");
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
fn diagnostic_contracts_are_active() {
    let contract_root = root().join("../contracts");
    let text = std::fs::read_to_string(contract_root.join("active.json"))
        .expect("failed to read active diagnostic contracts");
    let contract: Value = serde_json::from_str(&text).expect("invalid active contract JSON");
    assert_eq!(contract["status"], "active");
    let cases = contract["cases"].as_array().expect("active contract cases missing");
    assert_eq!(cases.len(), 7);
    let mut ids = HashSet::new();
    for case in cases {
        let id = field(case, "id");
        assert!(ids.insert(id), "duplicate active contract: {id}");
        let source = contract_root.join(field(case, "source"));
        assert!(source.is_file(), "active source does not exist: {id}");
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

#[test]
fn malformed_corpus_scopes_preserve_source_error_and_incomplete_reports() {
    for case in manifest() {
        if field(&case, "compiler_class") != "syntax_error" {
            continue;
        }
        let observed = observed_evidence(&case);
        assert!(!observed.analyzed);
        assert_eq!(observed.scope_kind, ScopeKind::SourceRecovery);
        assert!(observed.syntax_error);
        assert!(observed.incomplete);
        assert!(observed.findings.is_empty());
    }
}
