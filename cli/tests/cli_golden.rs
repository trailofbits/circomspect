use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

struct GoldenCase {
    name: &'static str,
    source: &'static str,
    args: &'static [&'static str],
    status: i32,
}

const CASES: &[GoldenCase] = &[
    GoldenCase { name: "library_no_main", source: "library_item.circom", args: &[], status: 0 },
    GoldenCase {
        name: "partial_library",
        source: "recoverable_library.circom",
        args: &[],
        status: 1,
    },
    GoldenCase { name: "missing_include", source: "missing_include.circom", args: &[], status: 1 },
    GoldenCase {
        name: "secondary_location",
        source: "secondary_location.circom",
        args: &[],
        status: 1,
    },
    GoldenCase {
        name: "missing_callee_order",
        source: "unresolved_library.circom",
        args: &["--level", "error"],
        status: 1,
    },
    GoldenCase {
        name: "malformed_input",
        source: "lexical_error_library.circom",
        args: &[],
        status: 1,
    },
    GoldenCase {
        name: "locationless_error",
        source: "unsupported_version.circom",
        args: &[],
        status: 1,
    },
    GoldenCase {
        name: "allow_suppression",
        source: "unresolved_library.circom",
        args: &["--allow", "CS0019", "--level", "error"],
        status: 0,
    },
    GoldenCase {
        name: "level_filter",
        source: "unversioned_library.circom",
        args: &["--level", "error"],
        status: 0,
    },
];

fn fixture_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

fn normalize_sarif(value: &mut Value, fixture_root: &Path) {
    match value {
        Value::Array(items) => {
            for item in items {
                normalize_sarif(item, fixture_root);
            }
        }
        Value::Object(fields) => {
            for item in fields.values_mut() {
                normalize_sarif(item, fixture_root);
            }
        }
        Value::String(text) => {
            let prefix = format!("file://{}/", fixture_root.display());
            if let Some(relative) = text.strip_prefix(&prefix) {
                *text = format!("file:///fixtures/{relative}");
            } else {
                let root = fixture_root.display().to_string();
                *text = text.replace(&root, "/fixtures");
            }
        }
        Value::Null | Value::Bool(_) | Value::Number(_) => {}
    }
}

fn normalize_rule_order(value: &mut Value) {
    let Some(rules) = value.pointer_mut("/runs/0/tool/driver/rules").and_then(Value::as_array_mut)
    else {
        return;
    };
    rules.sort_by(|left, right| {
        let left = left.get("id").and_then(Value::as_str).expect("rule has no ID");
        let right = right.get("id").and_then(Value::as_str).expect("rule has no ID");
        left.cmp(right)
    });
}

fn normalize_analysis_log(stdout: &str) -> String {
    let mut lines: Vec<&str> = stdout.lines().collect();
    let mut analysis_lines: Vec<&str> =
        lines.iter().copied().filter(|line| line.starts_with("circomspect: analyzing ")).collect();
    analysis_lines.sort_unstable();
    let mut sorted = analysis_lines.into_iter();
    for line in &mut lines {
        if line.starts_with("circomspect: analyzing ") {
            *line = sorted.next().expect("analysis line count changed");
        }
    }
    let mut normalized = lines.join("\n");
    if stdout.ends_with('\n') {
        normalized.push('\n');
    }
    normalized
}

fn run_case(case: &GoldenCase) {
    let root = fixture_root();
    let source = root.join(case.source);
    let sarif_path = std::env::temp_dir().join(format!(
        "circomspect-golden-{}-{}.sarif",
        std::process::id(),
        case.name
    ));
    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .arg(&source)
        .args(case.args)
        .arg("--sarif-file")
        .arg(&sarif_path)
        .output()
        .expect("failed to run Circomspect");
    assert_eq!(output.status.code(), Some(case.status), "{}", case.name);
    assert!(output.stderr.is_empty(), "{}: {:?}", case.name, output.stderr);
    let stdout = String::from_utf8(output.stdout).expect("CLI stdout is not UTF-8");
    let stdout = stdout
        .replace(&source.display().to_string(), "<fixture>")
        .replace(&sarif_path.display().to_string(), "<sarif>");
    let stdout = normalize_analysis_log(&stdout);
    let golden_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/goldens");
    let expected_stdout =
        std::fs::read_to_string(golden_root.join(format!("{}.stdout", case.name)))
            .expect("missing CLI stdout golden");
    assert_eq!(stdout, expected_stdout, "{} stdout changed", case.name);
    let sarif = std::fs::read_to_string(&sarif_path).expect("SARIF file was not written");
    std::fs::remove_file(&sarif_path).expect("failed to remove SARIF file");
    let mut sarif: Value = serde_json::from_str(&sarif).expect("invalid actual SARIF");
    normalize_sarif(&mut sarif, &root);
    normalize_rule_order(&mut sarif);
    let expected_sarif =
        std::fs::read_to_string(golden_root.join(format!("{}.sarif.json", case.name)))
            .expect("missing SARIF golden");
    let mut expected_sarif: Value =
        serde_json::from_str(&expected_sarif).expect("invalid SARIF golden");
    normalize_rule_order(&mut expected_sarif);
    assert_eq!(sarif, expected_sarif, "{} SARIF changed", case.name);
}

#[test]
fn current_cli_and_sarif_baseline() {
    for case in CASES {
        run_case(case);
    }
}
