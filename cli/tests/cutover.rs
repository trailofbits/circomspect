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
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

fn run(source: &Path, args: &[&str], name: &str) -> (i32, String, Value) {
    let sarif = std::env::temp_dir().join(format!(
        "circomspect-cutover-{name}-{}-{:?}.sarif",
        std::process::id(),
        std::thread::current().id()
    ));
    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .arg(source)
        .args(args)
        .arg("--sarif-file")
        .arg(&sarif)
        .output()
        .expect("run analyzer");
    assert!(output.stderr.is_empty(), "{:?}", output.stderr);
    let json = fs::read_to_string(&sarif).expect("SARIF exists even when empty");
    fs::remove_file(&sarif).expect("remove output");
    let stdout = String::from_utf8(output.stdout).expect("UTF-8 output");
    (output.status.code().expect("normal exit"), stdout, serde_json::from_str(&json).unwrap())
}

fn ids(sarif: &Value) -> BTreeSet<&str> {
    sarif["runs"][0]["results"]
        .as_array()
        .expect("results")
        .iter()
        .map(|result| result["ruleId"].as_str().expect("rule ID"))
        .collect()
}

fn fixture(name: &str, source: &str) -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-cutover-{name}-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("main.circom");
    fs::write(&path, source).unwrap();
    path
}

#[test]
fn new_diagnostic_contracts_preserve_filtering_levels_and_exit_status() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../tests/contracts");
    let manifest: Value =
        serde_json::from_str(&fs::read_to_string(root.join("active.json")).unwrap()).unwrap();
    for case in manifest["cases"].as_array().unwrap() {
        let args: Vec<_> =
            case["args"].as_array().unwrap().iter().map(|value| value.as_str().unwrap()).collect();
        let (status, stdout, sarif) =
            run(&root.join(case["source"].as_str().unwrap()), &args, case["id"].as_str().unwrap());
        assert_eq!(
            status,
            i32::try_from(case["expected_exit_code"].as_i64().unwrap()).unwrap(),
            "{stdout}"
        );
        let expected: BTreeSet<_> = case["expected_rule_ids"]
            .as_array()
            .unwrap()
            .iter()
            .map(|value| value.as_str().unwrap())
            .collect();
        assert_eq!(ids(&sarif), expected, "{stdout}");
        for result in sarif["runs"][0]["results"].as_array().unwrap() {
            let id = result["ruleId"].as_str().unwrap();
            assert_eq!(result["level"], case["expected_sarif_levels"][id]);
            assert!(!result["locations"].as_array().unwrap().is_empty());
        }
    }
}

#[test]
fn owned_bus_syntax_reaches_semantic_diagnostics() {
    let path = fixture(
        "bus",
        "pragma circom 2.2.3;\nbus Pair(){signal x;}\n\
        template Good(){signal output out;out<==1;}\n\
        template Bad(){MissingBus() value;}\n",
    );
    let (status, stdout, sarif) = run(&path, &["--level", "error"], "bus");
    assert_eq!(status, 1, "{stdout}");
    assert!(ids(&sarif).contains("CS0022"), "{stdout}");
    assert!(!ids(&sarif).contains("P1000"), "{stdout}");
    assert!(stdout.contains("analyzing template 'Good'"), "{stdout}");
}

#[test]
fn standalone_bus_library_reports_incomplete_without_main() {
    let path = fixture("bus-only", "pragma circom 2.2.3;\nbus Pair(){signal x;}\n");
    let (status, stdout, sarif) = run(&path, &[], "bus-only");
    assert_eq!(status, 1, "{stdout}");
    assert_eq!(ids(&sarif), BTreeSet::from(["CS0020"]), "{stdout}");
    assert_eq!(sarif["runs"][0]["results"].as_array().unwrap().len(), 1);
}

#[test]
fn invalid_expression_statement_keeps_later_library_diagnostics() {
    let path = fixture(
        "expression-recovery",
        "pragma circom 2.2.3;\nfunction F() {\n    1;\n    return Missing();\n}\n\
         function Neighbor() { return 0; }\n",
    );
    for (name, args) in [
        ("expression-recovery", &[][..]),
        ("expression-recovery-errors", &["--level", "error"][..]),
    ] {
        let (status, stdout, sarif) = run(&path, args, name);
        assert_eq!(status, 1, "{stdout}");
        assert!(stdout.contains("analyzing function 'F'"), "{stdout}");
        assert!(stdout.contains("analyzing function 'Neighbor'"), "{stdout}");
        let results = sarif["runs"][0]["results"].as_array().unwrap();
        let syntax: Vec<_> = results.iter().filter(|result| result["ruleId"] == "P1000").collect();
        assert_eq!(syntax.len(), 1, "{stdout}");
        assert_eq!(syntax[0]["level"], "error");
        assert_eq!(
            syntax[0]["message"]["text"],
            "only an anonymous component call may be used as an expression statement"
        );
        assert_eq!(
            syntax[0]["locations"][0]["physicalLocation"]["region"],
            serde_json::json!({"startLine": 3, "startColumn": 5, "endLine": 3, "endColumn": 7})
        );
        let missing: Vec<_> =
            results.iter().filter(|result| result["ruleId"] == "CS0019").collect();
        assert_eq!(missing.len(), 1, "{stdout}");
        assert_eq!(missing[0]["level"], "error");
        assert_eq!(missing[0]["message"]["text"], "unresolved Function call `Missing`");
        assert_eq!(
            missing[0]["locations"][0]["physicalLocation"]["region"],
            serde_json::json!({"startLine": 4, "startColumn": 12, "endLine": 4, "endColumn": 19})
        );
        if args.is_empty() {
            let order: Vec<_> = results.iter().map(|result| &result["ruleId"]).collect();
            assert_eq!(order, ["P1000", "CS0019", "CS0020"]);
            assert!(stdout.contains("3 issues found."), "{stdout}");
        } else {
            assert_eq!(results.len(), 2, "{stdout}");
            assert!(stdout.contains("2 issues found."), "{stdout}");
        }
    }
}

#[test]
fn unsupported_library_definitions_have_scoped_incomplete_diagnostics() {
    for (name, declaration, column) in [
        ("standalone-bus", "bus Pair(){signal x;}", 5),
        ("unsupported-bus", "bus Pair(){signal x;return 1;}", 5),
        ("unused-custom", "template custom Native(){signal output out;}", 17),
    ] {
        let path = fixture(
            name,
            &format!(
                "pragma circom 2.2.3; pragma custom_templates;\n{declaration}\n\
                 template Good(){{signal output out;out<==1;}}\n"
            ),
        );
        let (status, stdout, sarif) = run(&path, &[], name);
        assert_eq!(status, 1, "{stdout}");
        assert!(!stdout.contains("No issues found"), "{stdout}");
        assert!(stdout.contains("analyzing template 'Good'"), "{stdout}");
        let results = sarif["runs"][0]["results"].as_array().unwrap();
        let incomplete: Vec<_> =
            results.iter().filter(|result| result["ruleId"] == "CS0020").collect();
        assert_eq!(incomplete.len(), 1, "{stdout}");
        let region = &incomplete[0]["locations"][0]["physicalLocation"]["region"];
        assert_eq!(region["startLine"], 2, "{stdout}");
        assert_eq!(region["startColumn"], column, "{stdout}");
    }
}

#[test]
fn missing_input_file_is_visible_in_terminal_and_sarif() {
    let path = fixture("missing", "").with_file_name("absent.circom");
    let (status, stdout, sarif) = run(&path, &[], "missing");
    assert_eq!(status, 1);
    assert!(stdout.contains("absent.circom"));
    assert!(ids(&sarif).contains("P1000"));
}

#[test]
fn include_cycles_have_source_locations_and_terminate() {
    let path = fixture("cycle", "pragma circom 2.2.3; include \"child.circom\"; template Good(){}");
    fs::write(path.with_file_name("child.circom"), "pragma circom 2.2.3; include \"main.circom\";")
        .unwrap();
    let (status, stdout, sarif) = run(&path, &["--level", "error"], "cycle");
    assert_eq!(status, 1, "{stdout}");
    let results = sarif["runs"][0]["results"].as_array().unwrap();
    assert_eq!(results.len(), 1, "{stdout}");
    assert!(results[0]["message"]["text"].as_str().unwrap().contains("cyclic include"));
    assert_eq!(results[0]["locations"][0]["physicalLocation"]["region"]["startLine"], 1);
}

#[test]
fn concrete_main_arguments_reach_numeric_rules() {
    let path = fixture(
        "main-argument",
        "pragma circom 2.2.3;\n\
        template Main(n){signal output out; if(n){out<==1;}else{out<==0;}}\n\
        component main=Main(1);\n",
    );
    let (_, stdout, sarif) = run(&path, &[], "main-argument");
    assert!(ids(&sarif).contains("CS0009"), "{stdout}");
}

#[test]
fn directory_inputs_preserve_root_diagnostics_and_skip_non_circom_files() {
    let path = fixture("directory", "pragma circom 2.2.3; template Root(){component c=Missing();}");
    fs::create_dir_all(path.parent().unwrap().join("nested")).unwrap();
    fs::write(
        path.parent().unwrap().join("nested/child.circom"),
        "pragma circom 2.2.3; template Nested(){component c=OtherMissing();}",
    )
    .unwrap();
    fs::write(path.with_file_name("notes.txt"), "invalid text").unwrap();
    let (status, stdout, sarif) = run(path.parent().unwrap(), &["--level", "error"], "directory");
    assert_eq!(status, 1, "{stdout}");
    assert_eq!(ids(&sarif), BTreeSet::from(["CS0019"]));
    assert_eq!(sarif["runs"][0]["results"].as_array().unwrap().len(), 2);
    assert!(stdout.contains("analyzing template 'Root'"));
    assert!(stdout.contains("analyzing template 'Nested'"));
}

#[test]
fn repeated_runs_preserve_exact_sarif_order_and_source_spans() {
    let path = fixture(
        "repeat",
        "pragma circom 2.2.3;\n\
        template First(){component c=Missing();}\n\
        template Second(){component c=Other();}\n",
    );
    let (_, first_stdout, first) = run(&path, &[], "repeat");
    let (_, second_stdout, second) = run(&path, &[], "repeat");
    assert_eq!(first_stdout, second_stdout);
    assert_eq!(first, second);
    let results = first["runs"][0]["results"].as_array().unwrap();
    let missing = results.iter().find(|result| result["ruleId"] == "CS0019").unwrap();
    let region = &missing["locations"][0]["physicalLocation"]["region"];
    assert_eq!(region["startLine"], 2);
    assert_eq!(region["startColumn"], 30);
    assert_eq!(region["endColumn"], 37);
}

#[test]
fn selected_curve_changes_certified_arithmetic_results() {
    let path = fixture(
        "curve",
        "pragma circom 2.2.3;\n\
        template Main(){signal output out;out<==18446744069414584320+1;}\n\
        component main=Main();\n",
    );
    let (_, _, bn254) = run(&path, &["--curve", "BN254", "--level", "info"], "curve-bn254");
    let (_, _, gold) = run(&path, &["--curve", "GOLDILOCKS", "--level", "info"], "curve-gold");
    assert!(!ids(&bn254).contains("CS0004"));
    assert!(ids(&gold).contains("CS0004"));
}

#[test]
fn incomplete_scopes_keep_distinct_call_paths_and_group_rule_reasons() {
    let path = fixture(
        "contexts",
        "pragma circom 2.2.3;\n\
        template Child(){signal input x;signal output y;y<--x*x;y===x*x;}\n\
        template Main(){component a=Child();a.x<==1;component b=Child();b.x<==2;}\n\
        component main=Main();\n",
    );
    let (_, stdout, sarif) = run(&path, &[], "contexts");
    let results = sarif["runs"][0]["results"].as_array().unwrap();
    let child: Vec<_> = results
        .iter()
        .filter(|result| {
            result["ruleId"] == "CS0020"
                && result["locations"][0]["physicalLocation"]["region"]["startLine"] == 2
        })
        .collect();
    assert_eq!(child.len(), 2, "{stdout}");
    for result in &child {
        let related = result["relatedLocations"].as_array().unwrap();
        assert!(related
            .iter()
            .any(|label| label["message"]["text"].as_str().unwrap().contains("CS0004")));
        assert!(related.iter().any(|label| label["message"]["text"]
            .as_str()
            .unwrap()
            .contains("Reached through this call")));
    }
    assert_ne!(child[0]["relatedLocations"], child[1]["relatedLocations"]);
}

#[test]
fn incomplete_source_scope_coalesces_identical_locations_and_reasons() {
    let path =
        fixture("incomplete-labels", "pragma circom 2.2.3;\ntemplate Broken(){\nvar value=;\n}\n");
    let (_, stdout, sarif) = run(&path, &[], "incomplete-labels");
    let results = sarif["runs"][0]["results"].as_array().unwrap();
    let incomplete: Vec<_> = results.iter().filter(|result| result["ruleId"] == "CS0020").collect();
    assert_eq!(incomplete.len(), 1, "{stdout}");
    let related = incomplete[0]["relatedLocations"].as_array().unwrap();
    let bodies: Vec<_> = related
        .iter()
        .filter(|label| {
            let region = &label["physicalLocation"]["region"];
            region["startLine"] == 2 && region["endLine"] == 4
        })
        .collect();
    assert_eq!(bodies.len(), 1, "{stdout}");
    let message = bodies[0]["message"]["text"].as_str().unwrap();
    for id in ["CS0003", "CS0004", "CS0009", "CS0010", "CS0015", "CS0016"] {
        assert!(message.contains(id), "{message}");
    }
}

#[test]
fn library_roots_are_independent_of_declaration_order() {
    let child = "template Child(n){signal output y;if(n){y<==1;}else{y<==0;}}";
    let wrapper = "template Wrapper(){component child=Child(1);}";
    for (name, declarations) in [
        ("library-child-first", format!("{child}\n{wrapper}")),
        ("library-wrapper-first", format!("{wrapper}\n{child}")),
    ] {
        let path = fixture(name, &format!("pragma circom 2.2.3;\n{declarations}\n"));
        let (_, stdout, sarif) = run(&path, &[], name);
        let results = sarif["runs"][0]["results"].as_array().unwrap();
        assert!(results.iter().any(|result| result["ruleId"] == "CS0009"), "{stdout}");
        let symbolic_child = results.iter().any(|result| {
            if result["ruleId"] != "CS0020" {
                return false;
            }
            let related = result["relatedLocations"].as_array().unwrap();
            let messages: Vec<_> =
                related.iter().map(|label| label["message"]["text"].as_str().unwrap()).collect();
            messages.iter().any(|message| message.contains("CS0009"))
                && messages.iter().all(|message| !message.contains("Reached through this call"))
        });
        assert!(symbolic_child, "independent symbolic Child root missing: {stdout}");
    }
}

#[test]
fn failed_sarif_write_returns_a_visible_error_and_failure_exit() {
    let path = fixture("bad-sarif", "pragma circom 2.2.3;template Main(){}");
    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .arg(&path)
        .args(["--level", "error", "--allow", "T3001", "--sarif-file"])
        .arg(path.parent().unwrap())
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("Cannot write SARIF"), "{stdout}");
    assert!(!stdout.contains("No issues found"));
}

#[test]
fn empty_sarif_is_written_without_a_result_written_status() {
    let path = fixture("empty-sarif", "pragma circom 2.2.3;template Main(){}");
    let (status, stdout, sarif) = run(&path, &[], "empty-sarif");
    assert_eq!(status, 0, "{stdout}");
    assert_eq!(sarif["runs"][0]["results"].as_array().unwrap().len(), 0);
    assert!(stdout.contains("No issues found"), "{stdout}");
    assert!(!stdout.contains("Result written"), "{stdout}");
}

#[test]
fn multiple_main_files_report_both_source_locations() {
    let path =
        fixture("multiple-main", "pragma circom 2.2.3; template First(){} component main=First();");
    let other = path.with_file_name("other.circom");
    fs::write(&other, "pragma circom 2.2.3; template Second(){} component main=Second();").unwrap();
    let (_, stdout, sarif) = run(path.parent().unwrap(), &["--level", "error"], "multiple-main");
    assert_eq!(ids(&sarif), BTreeSet::from(["P1002"]), "{stdout}");
    let report = &sarif["runs"][0]["results"][0];
    assert_eq!(report["locations"].as_array().unwrap().len(), 1);
    assert_eq!(report["relatedLocations"].as_array().unwrap().len(), 1);
    assert_ne!(report["locations"][0]["id"], report["relatedLocations"][0]["id"]);
}

#[test]
#[cfg(unix)]
fn sarif_file_uris_preserve_reserved_and_unicode_file_names() {
    let path = fixture("file-uri", "pragma circom 2.2.3;template Main(){Missing();}");
    let renamed = path.with_file_name("space # % \" å.circom");
    fs::rename(path, &renamed).unwrap();
    let (status, stdout, sarif) = run(&renamed, &["--level", "error"], "file-uri");
    assert_eq!(status, 1, "{stdout}");
    assert!(stdout.contains("space # % \" å.circom"));
    let location = &sarif["runs"][0]["results"][0]["locations"][0]["physicalLocation"];
    let uri = location["artifactLocation"]["uri"].as_str().unwrap();
    assert!(uri.starts_with("file:///"), "{uri}");
    assert!(uri.ends_with("/space%20%23%20%25%20%22%20%C3%A5.circom"), "{uri}");
    assert_eq!(location["region"]["startLine"], 1);
}

#[test]
fn sarif_columns_use_declared_unicode_code_points() {
    let source = "pragma circom 2.2.3;\n/* 🦀 */ template Main(){component c=Missing();}\n";
    let path = fixture("unicode-column", source);
    let (_, _, sarif) = run(&path, &["--level", "error"], "unicode-column");
    assert_eq!(sarif["runs"][0]["columnKind"], "unicodeCodePoints");
    let region = &sarif["runs"][0]["results"][0]["locations"][0]["physicalLocation"]["region"];
    assert_eq!(region["startLine"], 2);
    assert_eq!(region["startColumn"], 37);
    assert_eq!(region["endColumn"], 44);
}

#[test]
fn a_missing_explicit_library_file_is_reported_even_without_an_include() {
    let path = fixture("library-missing", "pragma circom 2.2.3; template Main(){}");
    let missing = path.with_file_name("missing.circom");
    let (status, stdout, sarif) = run(
        &path,
        &["--level", "error", "--library", missing.to_str().unwrap()],
        "library-missing",
    );
    assert_eq!(status, 1, "{stdout}");
    assert!(ids(&sarif).contains("P1000"));
    assert!(stdout.contains("missing.circom"));
}

#[test]
#[cfg(unix)]
fn closed_stdout_reports_an_io_error_without_panicking() {
    use std::process::Stdio;

    let path = fixture("closed-stdout", "pragma circom 2.2.3; template Main(){}");
    let missing = path.with_file_name("missing.circom");
    for input in [Some(path), Some(missing), None] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_circomspect"));
        if let Some(path) = input {
            command.arg(path);
        }
        let mut child = command.stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
        drop(child.stdout.take());
        let output = child.wait_with_output().unwrap();
        assert_eq!(output.status.code(), Some(1));
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(stderr.contains("stdout"), "{stderr}");
        assert!(!stderr.contains("panicked"), "{stderr}");
    }
}
