// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
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
    GoldenCase {
        name: "expression_recovery",
        source: "expression_recovery.circom",
        args: &[],
        status: 1,
    },
    GoldenCase { name: "missing_include", source: "missing_include.circom", args: &[], status: 1 },
    GoldenCase {
        name: "secondary_location",
        source: "secondary_location.circom",
        args: &[],
        status: 0,
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
        name: "unsupported_version",
        source: "unsupported_version.circom",
        args: &[],
        status: 1,
    },
    GoldenCase { name: "locationless_error", source: "absent_input.circom", args: &[], status: 1 },
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
            let prefix = url::Url::from_directory_path(fixture_root).unwrap().to_string();
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
    let golden_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/goldens");
    let expected_stdout =
        std::fs::read_to_string(golden_root.join(format!("{}.stdout", case.name)))
            .expect("missing CLI stdout golden");
    assert_eq!(stdout, expected_stdout, "{} stdout changed", case.name);
    let sarif = std::fs::read_to_string(&sarif_path).expect("SARIF file was not written");
    std::fs::remove_file(&sarif_path).expect("failed to remove SARIF file");
    let mut sarif: Value = serde_json::from_str(&sarif).expect("invalid actual SARIF");
    normalize_sarif(&mut sarif, &root);
    let expected_sarif =
        std::fs::read_to_string(golden_root.join(format!("{}.sarif.json", case.name)))
            .expect("missing SARIF golden");
    let expected_sarif: Value =
        serde_json::from_str(&expected_sarif).expect("invalid SARIF golden");
    assert_eq!(sarif, expected_sarif, "{} SARIF changed", case.name);
}

#[test]
fn current_cli_and_sarif_baseline() {
    for case in CASES {
        run_case(case);
    }
}
