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
        assert_eq!(status, case["expected_exit_code"].as_i64().unwrap() as i32, "{stdout}");
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
        .args(["--level", "error", "--sarif-file"])
        .arg(path.parent().unwrap())
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("Cannot write SARIF"), "{stdout}");
    assert!(!stdout.contains("No issues found"));
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
