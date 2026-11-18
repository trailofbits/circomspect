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
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

use serde_json::Value;

#[derive(Debug)]
struct CliRun {
    status: ExitStatus,
    stdout: String,
    stderr: String,
    sarif: Value,
}

struct TemporaryDirectory {
    path: PathBuf,
}

impl TemporaryDirectory {
    fn new(name: &str) -> Self {
        static NEXT_DIRECTORY: AtomicUsize = AtomicUsize::new(0);
        loop {
            let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir()
                .join(format!("circomspect-cutover-{name}-{}-{sequence}", std::process::id()));
            match fs::create_dir(&path) {
                Ok(()) => return Self { path },
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
                Err(error) => panic!("create fixture directory {}: {error}", path.display()),
            }
        }
    }
}

impl Drop for TemporaryDirectory {
    fn drop(&mut self) {
        if let Err(error) = fs::remove_dir_all(&self.path) {
            // Preserve the original test failure instead of aborting on a second panic.
            assert!(
                std::thread::panicking(),
                "remove fixture directory {}: {error}",
                self.path.display()
            );
        }
    }
}

struct SourceFixture {
    directory: TemporaryDirectory,
}

impl SourceFixture {
    fn path(&self) -> PathBuf {
        self.directory.path.join("main.circom")
    }
}

fn run(source: &Path, args: &[&str], name: &str) -> CliRun {
    let result = try_run(source, args, name).unwrap_or_else(|error| panic!("{error}"));
    assert!(result.stderr.is_empty());
    result
}

fn try_run(source: &Path, args: &[&str], name: &str) -> Result<CliRun, String> {
    let directory = TemporaryDirectory::new(name);
    let sarif = directory.path.join("output.sarif");
    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .arg(source)
        .args(args)
        .arg("--sarif-file")
        .arg(&sarif)
        .output()
        .map_err(|error| format!("run analyzer for {}: {error}", source.display()))?;
    let mut result = decode_output(&output, &sarif)?;
    // Each run owns a unique output directory; retain comparison of all stable terminal text.
    result.stdout = result.stdout.replace(&sarif.display().to_string(), "<sarif>");
    Ok(result)
}

fn decode_output(output: &Output, sarif: &Path) -> Result<CliRun, String> {
    if output.status.code().is_none() {
        return Err(output_error(output, "analyzer terminated without an exit code"));
    }
    if !output.stderr.is_empty() {
        return Err(output_error(output, "analyzer wrote unexpected stderr"));
    }
    let json = fs::read_to_string(sarif).map_err(|error| {
        output_error(output, &format!("read SARIF {}: {error}", sarif.display()))
    })?;
    let sarif = serde_json::from_str(&json)
        .map_err(|error| output_error(output, &format!("decode SARIF: {error}")))?;
    let stdout = std::str::from_utf8(&output.stdout)
        .map_err(|error| output_error(output, &format!("decode stdout as UTF-8: {error}")))?
        .to_owned();
    Ok(CliRun { status: output.status, stdout, stderr: String::new(), sarif })
}

fn output_error(output: &Output, operation: &str) -> String {
    format!(
        "{operation}\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    )
}

fn ids(sarif: &Value) -> BTreeSet<&str> {
    sarif["runs"][0]["results"]
        .as_array()
        .expect("results")
        .iter()
        .map(|result| result["ruleId"].as_str().expect("rule ID"))
        .collect()
}

fn fixture(name: &str, source: &str) -> SourceFixture {
    let input = SourceFixture { directory: TemporaryDirectory::new(name) };
    fs::write(input.path(), source).expect("write fixture source");
    input
}

struct ContractCase {
    id: String,
    source: PathBuf,
    args: Vec<String>,
    exit_code: i32,
    rule_ids: BTreeSet<String>,
    levels: BTreeMap<String, String>,
}

impl ContractCase {
    fn from_json(case: &Value) -> Self {
        let mut args = Vec::new();
        for arg in case["args"].as_array().expect("contract args array") {
            args.push(arg.as_str().expect("contract argument string").to_owned());
        }
        let mut rule_ids = BTreeSet::new();
        for id in case["expected_rule_ids"].as_array().expect("contract rule IDs array") {
            rule_ids.insert(id.as_str().expect("contract rule ID string").to_owned());
        }
        let mut levels = BTreeMap::new();
        for (id, level) in case["expected_sarif_levels"].as_object().expect("contract levels map") {
            levels.insert(id.clone(), level.as_str().expect("contract level string").to_owned());
        }
        Self {
            id: case["id"].as_str().expect("contract ID string").to_owned(),
            source: PathBuf::from(case["source"].as_str().expect("contract source path")),
            args,
            exit_code: i32::try_from(
                case["expected_exit_code"].as_i64().expect("contract exit code"),
            )
            .expect("contract exit code fits i32"),
            rule_ids,
            levels,
        }
    }
}

#[test]
fn fixture_directory_is_removed_on_scope_exit() {
    let input = fixture("cleanup", "pragma circom 2.2.3;");
    let path = input.path();
    let directory = path.parent().unwrap().to_path_buf();
    assert!(directory.exists());
    drop(input);
    assert!(!directory.exists(), "fixture leaked {}", directory.display());
}

#[test]
fn fixtures_own_distinct_directories_and_clean_up_during_unwinding() {
    let first = fixture("unique", "first");
    let second = fixture("unique", "second");
    let path = second.path();
    assert_ne!(first.path(), path);
    let result = std::panic::catch_unwind(move || {
        let _second = second;
        panic!("test failure while a fixture is alive");
    });
    assert!(result.is_err());
    assert!(!path.parent().unwrap().exists());
    assert_eq!(fs::read_to_string(first.path()).unwrap(), "first");
}

#[test]
fn fixture_cleanup_failure_is_visible_without_double_panicking() {
    let first = fixture("cleanup-error", "first");
    fs::remove_dir_all(&first.directory.path).unwrap();
    assert!(std::panic::catch_unwind(move || drop(first)).is_err());

    let second = fixture("cleanup-unwind", "second");
    fs::remove_dir_all(&second.directory.path).unwrap();
    let error = std::panic::catch_unwind(move || {
        let _second = second;
        panic!("original failure");
    })
    .unwrap_err();
    assert_eq!(error.downcast_ref::<&str>(), Some(&"original failure"));
}

#[test]
fn invalid_cli_arguments_retain_process_failure_evidence() {
    let input = fixture("bad-option", "pragma circom 2.2.3;");
    let status = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .arg("--nonexistent-option")
        .output()
        .unwrap()
        .status;
    assert_eq!(status.code(), Some(2));
    let error = try_run(&input.path(), &["--nonexistent-option"], "bad-option").unwrap_err();
    assert!(error.contains("unexpected stderr"), "{error}");
    assert!(error.contains(&format!("status: {status}")), "{error}");
    assert!(error.contains("stdout:\n"), "{error}");
    assert!(error.contains("stderr:\nerror: unexpected argument"), "{error}");
    assert!(error.contains("--nonexistent-option"), "{error}");
}

#[test]
fn missing_and_invalid_sarif_retain_status_and_both_streams() {
    let directory = TemporaryDirectory::new("decode-errors");
    let sarif = directory.path.join("output.sarif");
    for expected in ["read SARIF", "decode SARIF"] {
        let output =
            Command::new(env!("CARGO_BIN_EXE_circomspect")).arg("--help").output().unwrap();
        assert_eq!(output.status.code(), Some(0));
        let status = output.status;
        let error = decode_output(&output, &sarif).unwrap_err();
        assert!(error.contains(expected), "{error}");
        assert!(error.contains(&format!("status: {status}")), "{error}");
        assert!(error.contains("stdout:\n"), "{error}");
        assert!(error.contains("Usage:"), "{error}");
        assert!(error.contains("stderr:\n"), "{error}");
        fs::write(&sarif, "invalid JSON").unwrap();
    }
}

#[test]
#[cfg(unix)]
fn signal_termination_retains_the_signal_and_process_streams() {
    use std::os::unix::process::ExitStatusExt;

    let output = Output {
        status: ExitStatus::from_raw(9),
        stdout: b"before signal".to_vec(),
        stderr: b"signal details".to_vec(),
    };
    let error = decode_output(&output, Path::new("unused.sarif")).unwrap_err();
    assert!(error.contains("terminated without an exit code"), "{error}");
    assert!(error.contains("signal: 9"), "{error}");
    assert!(error.contains("stdout:\nbefore signal"), "{error}");
    assert!(error.contains("stderr:\nsignal details"), "{error}");
    assert!(!error.contains("read SARIF"), "{error}");
}

#[test]
fn diagnostic_contracts_preserve_filtering_levels_and_exit_status() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../tests/contracts");
    let manifest: Value =
        serde_json::from_str(&fs::read_to_string(root.join("active.json")).unwrap()).unwrap();
    let cases: Vec<_> = manifest["cases"]
        .as_array()
        .expect("contract cases array")
        .iter()
        .map(ContractCase::from_json)
        .collect();
    for case in cases {
        let args: Vec<_> = case.args.iter().map(String::as_str).collect();
        let CliRun { status, stdout, sarif, .. } = run(&root.join(case.source), &args, &case.id);
        assert_eq!(status.code(), Some(case.exit_code), "{stdout}");
        let expected: BTreeSet<_> = case.rule_ids.iter().map(String::as_str).collect();
        assert_eq!(ids(&sarif), expected, "{stdout}");
        for result in sarif["runs"][0]["results"].as_array().unwrap() {
            let id = result["ruleId"].as_str().unwrap();
            assert_eq!(result["level"].as_str(), Some(case.levels[id].as_str()));
            assert!(!result["locations"].as_array().unwrap().is_empty());
        }
    }
}

#[test]
fn diagnostics_are_interleaved_with_analysis_progress() {
    let input = fixture(
        "streamed-reports",
        "pragma circom 2.2.3;\n\
        template Broken(){component c=Missing();}\n\
        template Early(){var dead=1;signal output out;out<==0;}\n\
        template Later(){signal output out;out<==1;} component main=Broken();",
    );
    let result = run(&input.path(), &[], "streamed-reports");
    let position = |text: &str| result.stdout.find(text).unwrap();
    assert!(position("error: unresolved Template") < position("preparing analysis"));
    assert!(position("warning: Assigned value of `dead`") < position("analyzing template 'Later'"));
    assert_eq!(result.stdout.matches("warning: Assigned value of `dead`").count(), 1);
}

#[test]
fn irrelevant_contexts_stay_hidden_at_all_levels_without_changing_finding_filters() {
    let input = fixture(
        "streamed-contexts",
        "pragma circom 2.2.3;\n\
        template Child(n){var dead=1;signal output out;out<==n;}\n\
        template Main(){component a=Child(1);component b=Child(2);}\n\
        component main=Main();",
    );
    let default = run(&input.path(), &["--allow", "CS0008"], "streamed-contexts");
    let detailed =
        run(&input.path(), &["--level", "INFO", "--allow", "CS0008"], "streamed-contexts-info");
    let mut findings = Vec::new();
    for (result, continuations) in [(&default, 0), (&detailed, 0)] {
        assert_eq!(result.stdout.matches("warning: Assigned value of `dead`").count(), 1);
        assert_eq!(
            result.stdout.matches("Additional call paths for CS0006").count(),
            continuations
        );
        assert!(result.stdout.contains("1 finding reported."), "{}", result.stdout);
        assert_eq!(result.status.code(), Some(1), "{}", result.stdout);
        let reports = result.sarif["runs"][0]["results"].as_array().unwrap();
        let unused: Vec<_> = reports.iter().filter(|report| report["ruleId"] == "CS0006").collect();
        assert_eq!(unused.len(), 1);
        assert!(unused[0]["relatedLocations"].as_array().map_or(true, Vec::is_empty));
        findings.push(unused[0]);
    }
    assert_eq!(findings[0], findings[1]);
    for (args, expected_status) in [
        (&["--level", "ERROR"][..], Some(0)),
        (&["--allow", "CS0006", "--allow", "CS0008"][..], Some(0)),
        (&["--level", "INFO", "--allow", "CS0006", "--allow", "CS0008"][..], None),
    ] {
        let result = run(&input.path(), args, "filtered-contexts");
        assert!(!result.stdout.contains("Assigned value of `dead`"));
        assert!(!result.stdout.contains("Additional call paths"));
        assert!(!ids(&result.sarif).contains("CS0006"));
        if let Some(expected) = expected_status {
            assert_eq!(result.status.code(), Some(expected), "{}", result.stdout);
        }
    }
}

#[test]
fn missing_context_is_actionable_info_and_hidden_by_default() {
    let input = fixture(
        "context-info",
        "pragma circom 2.2.3;\n\
        function Count(n){var x;for(var i=0;i<n;i++){x=n>>i;if(x){log(x);}}return 0;}",
    );
    let default = run(&input.path(), &[], "context-default");
    assert_eq!(default.status.code(), Some(0), "{}", default.stdout);
    assert!(!ids(&default.sarif).contains("CS0020"), "{}", default.stdout);
    let detailed = run(&input.path(), &["-l", "INFO"], "context-info");
    let results = detailed.sarif["runs"][0]["results"].as_array().unwrap();
    let notices: Vec<_> = results.iter().filter(|result| result["ruleId"] == "CS0020").collect();
    assert!(!notices.is_empty(), "{}", detailed.stdout);
    assert!(notices.iter().all(|result| result["level"] == "note"));
    assert!(detailed.stdout.contains("parameter `n`"), "{}", detailed.stdout);
    assert!(detailed.stdout.contains("caller"), "{}", detailed.stdout);
    assert!(detailed.stdout.contains("analysis note"), "{}", detailed.stdout);
    assert!(!detailed.stdout.contains("could not be certified"));
}

#[test]
fn nonactionable_coverage_is_suppressed_even_at_info() {
    for source in [
        "pragma circom 2.2.3;\n\
        template Main(){signal input value;signal output out;out<==value+2;}\n\
        component main=Main();",
        "pragma circom 2.2.3;\n\
        template Library(unrelated){signal input value;signal output out;out<==value+2;}",
    ] {
        let input = fixture("nonactionable-coverage", source);
        let result = run(&input.path(), &["-l", "INFO"], "nonactionable-coverage");
        assert!(!ids(&result.sarif).contains("CS0020"), "{}", result.stdout);
        assert!(!result.stdout.contains("could not be certified"));
    }
}

#[test]
fn repeated_unused_value_is_reported_once_across_callers() {
    let input = fixture(
        "grouped-unused",
        "pragma circom 2.2.3;\n\
        template Child(n){var dead=1;signal output out;out<==n;}\n\
        template Main(){component a=Child(1);component b=Child(2);}\n\
        component main=Main();",
    );
    let result = run(&input.path(), &[], "grouped-unused");
    let results = result.sarif["runs"][0]["results"].as_array().unwrap();
    let unused: Vec<_> = results.iter().filter(|result| result["ruleId"] == "CS0006").collect();
    assert_eq!(unused.len(), 1, "{}", result.stdout);
    assert_eq!(result.stdout.matches("warning: Assigned value of `dead`").count(), 1);
    assert!(unused[0]["relatedLocations"].as_array().map_or(true, Vec::is_empty));
}

#[test]
fn source_literal_finding_omits_irrelevant_call_history() {
    let modulus = "21888242871839275222246405745257275088548364400416034343698204186575808495617";
    let input = fixture(
        "grouped-curve",
        &format!(
            "pragma circom 2.2.3;\n\
            template Child(n){{signal output out;out<==n+{modulus};}}\n\
            template Main(){{component a=Child(1);component b=Child(2);}}\n\
            component main=Main();"
        ),
    );
    let result = run(&input.path(), &["--curve", "BLS12_381"], "grouped-curve");
    let results = result.sarif["runs"][0]["results"].as_array().unwrap();
    let curve: Vec<_> = results.iter().filter(|result| result["ruleId"] == "CS0016").collect();
    assert_eq!(curve.len(), 1, "{}", result.stdout);
    assert!(curve[0]["relatedLocations"].as_array().map_or(true, Vec::is_empty));
}

#[test]
fn deferred_loop_guard_reports_incomplete_without_recursive_proof() {
    let input = fixture(
        "deferred-loop-guard",
        "pragma circom 2.2.3;\n\
        function F(n){var x;for(var i=0;i<n;i++){x=n>>i;if(x){log(x);}}return 0;}",
    );
    let result = run(&input.path(), &["-l", "INFO"], "deferred-loop-guard");
    assert_eq!(result.status.code(), Some(1), "{}", result.stdout);
    assert_eq!(ids(&result.sarif), BTreeSet::from(["CS0020"]), "{}", result.stdout);
}

#[test]
fn owned_bus_syntax_reaches_semantic_diagnostics() {
    let input = fixture(
        "bus",
        "pragma circom 2.2.3;\nbus Pair(){signal x;}\n\
        template Good(){signal output out;out<==1;}\n\
        template Bad(){MissingBus() value;} component main=Good();\n",
    );
    let path = input.path();
    let CliRun { status, stdout, sarif, .. } = run(&path, &["--level", "error"], "bus");
    assert_eq!(status.code(), Some(1), "{stdout}");
    assert!(ids(&sarif).contains("CS0022"), "{stdout}");
    assert!(!ids(&sarif).contains("P1000"), "{stdout}");
    assert!(stdout.contains("analyzing template 'Good'"), "{stdout}");
}

#[test]
fn standalone_bus_library_omits_nonactionable_analysis_notice() {
    let input = fixture("bus-only", "pragma circom 2.2.3;\nbus Pair(){signal x;}\n");
    let path = input.path();
    let CliRun { status, stdout, sarif, .. } = run(&path, &[], "bus-only");
    assert_eq!(status.code(), Some(0), "{stdout}");
    assert!(ids(&sarif).is_empty(), "{stdout}");
}

#[test]
fn invalid_expression_statement_keeps_later_source_diagnostics() {
    let input = fixture(
        "expression-recovery",
        "pragma circom 2.2.3;\nfunction F() {\n    1;\n    return Missing();\n}\n\
         function Neighbor() { return 0; }\n\
         template Main(){signal output out;out<==F();} component main=Main();\n",
    );
    let path = input.path();
    for (name, args) in [
        ("expression-recovery", &[][..]),
        ("expression-recovery-errors", &["--level", "error"][..]),
    ] {
        let CliRun { status, stdout, sarif, .. } = run(&path, args, name);
        assert_eq!(status.code(), Some(1), "{stdout}");
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
        let order: Vec<_> = results.iter().map(|result| &result["ruleId"]).collect();
        assert_eq!(order, ["P1000", "CS0019"]);
        assert!(stdout.contains("2 source errors reported."), "{stdout}");
    }
}

#[test]
fn unsupported_library_definitions_omit_nonactionable_notices() {
    for (name, declaration, status_code) in [
        ("standalone-bus", "bus Pair(){signal x;}", 0),
        ("unsupported-bus", "bus Pair(){signal x;return 1;}", 1),
        ("unused-custom", "template custom Native(){signal output out;}", 0),
    ] {
        let input = fixture(
            name,
            &format!(
                "pragma circom 2.2.3; pragma custom_templates;\n{declaration}\n\
                 template Good(){{signal output out;out<==1;}}\n"
            ),
        );
        let path = input.path();
        let CliRun { status, stdout, sarif, .. } = run(&path, &[], name);
        assert_eq!(status.code(), Some(status_code), "{stdout}");
        assert!(!stdout.contains("analysis limitation"), "{stdout}");
        assert!(stdout.contains("analyzing template 'Good'"), "{stdout}");
        let results = sarif["runs"][0]["results"].as_array().unwrap();
        let incomplete: Vec<_> =
            results.iter().filter(|result| result["ruleId"] == "CS0020").collect();
        assert!(incomplete.is_empty(), "{stdout}");
    }
}

#[test]
fn missing_input_file_is_visible_in_terminal_and_sarif() {
    let input = fixture("missing", "");
    let path = input.path().with_file_name("absent.circom");
    let CliRun { status, stdout, sarif, .. } = run(&path, &[], "missing");
    assert_eq!(status.code(), Some(1));
    assert!(stdout.contains("absent.circom"));
    assert!(ids(&sarif).contains("P1099"));
}

#[test]
fn include_cycles_terminate_without_source_errors() {
    let input =
        fixture("cycle", "pragma circom 2.2.3; include \"child.circom\"; template Good(){}");
    let path = input.path();
    fs::write(path.with_file_name("child.circom"), "pragma circom 2.2.3; include \"main.circom\";")
        .unwrap();
    let CliRun { status, stdout, sarif, .. } = run(&path, &["--level", "error"], "cycle");
    assert!(status.success(), "{stdout}");
    let results = sarif["runs"][0]["results"].as_array().unwrap();
    assert!(results.is_empty(), "{stdout}");
}

#[test]
fn partial_output_array_reports_assignment_and_constraint_warnings() {
    let input = fixture(
        "partial-output",
        "pragma circom 2.2.3; template Partial() { \
         signal input x; signal output out[4]; \
         out[0] <== x; out[1] <-- x; out[2] <== x; }",
    );
    let result = run(&input.path(), &[], "partial-output");
    assert!(ids(&result.sarif).contains("CS0024"), "{}", result.stdout);
    assert!(result.stdout.contains("out[1]"), "{}", result.stdout);
    assert!(result.stdout.contains("out[3]"), "{}", result.stdout);
    let messages: Vec<_> = result.sarif["runs"][0]["results"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|entry| entry["ruleId"] == "CS0024")
        .filter_map(|entry| entry["message"]["text"].as_str())
        .collect();
    assert_eq!(messages.len(), 2, "{}", result.stdout);
    assert!(messages.contains(&"Output `out[3]` is never assigned."));
    assert!(messages.contains(&"Output `out` has 2 elements without generated constraints."));
    assert!(messages
        .iter()
        .all(|message| !message.contains("out[0]") && !message.contains("out[2]")));
}

#[test]
fn complete_output_array_does_not_report_output_completeness() {
    let input = fixture(
        "complete-output",
        "pragma circom 2.2.3; template Complete() { \
         signal input x; signal output out[2]; out[0] <== x; out[1] <== x; }",
    );
    let result = run(&input.path(), &[], "complete-output");
    assert!(!ids(&result.sarif).contains("CS0024"), "{}", result.stdout);
}

#[test]
fn witness_dependent_assertion_is_reported_but_parameter_assertion_is_not() {
    let input = fixture(
        "witness-assert",
        "pragma circom 2.2.3; template Check(n) { \
         assert(n > 0); signal input x; signal output out; \
         assert(x == 1); out <== x; } component main = Check(1);",
    );
    let result = run(&input.path(), &[], "witness-assert");
    let messages: Vec<_> = result.sarif["runs"][0]["results"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|entry| entry["ruleId"] == "CS0023")
        .collect();
    assert_eq!(messages.len(), 1, "{}", result.stdout);
    assert!(result.stdout.contains("witness dependent values"), "{}", result.stdout);
}

#[test]
fn year_assertion_uses_plain_witness_dependent_warning() {
    let input = fixture(
        "year-assert",
        "pragma circom 2.2.3; template Check() {signal input year; signal output out; \
         assert(year <= 2030); out <== year;} component main = Check();",
    );
    let result = run(&input.path(), &[], "year-assert");
    let messages: Vec<_> = result.sarif["runs"][0]["results"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|entry| entry["ruleId"] == "CS0023")
        .filter_map(|entry| entry["message"]["text"].as_str())
        .collect();
    let expected = concat!(
        "This assertion checks witness dependent values during witness generation, ",
        "but it adds no constraint to the proof system."
    );
    assert_eq!(messages, [expected]);
    assert!(result.stdout.contains("This assertion does not constrain the proof."));
}

#[test]
fn assertion_repeated_by_a_mandatory_constraint_is_not_reported() {
    let input = fixture(
        "constrained-assert",
        "pragma circom 2.2.3; template Check() { \
         signal input x; signal output out; assert(x == 1); x === 1; out <== x; } \
         component main = Check();",
    );
    let result = run(&input.path(), &[], "constrained-assert");
    assert!(!ids(&result.sarif).contains("CS0023"), "{}", result.stdout);
}

#[test]
fn comparator_precondition_distinguishes_symbolic_and_exact_operands() {
    let input = fixture(
        "comparator-precondition",
        "pragma circom 2.2.3; \
         template LessThan(n) {assert(n <= 252); signal input in[2]; \
         signal output out; out <== in[0];} \
         template Check(max) {signal input x; signal output y; \
         y <== LessThan(8)([x, max + 1]);} component main = Check(256);",
    );
    let result = run(&input.path(), &[], "comparator-precondition");
    let messages: Vec<_> = result.sarif["runs"][0]["results"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|entry| entry["ruleId"] == "CS0025")
        .filter_map(|entry| entry["message"]["text"].as_str())
        .collect();
    assert!(messages.iter().any(|message| message.contains("input 1 is 257")));
    assert!(
        messages.contains(&"Failed to prove that `x` is constrained to be 8 bits."),
        "{messages:?}"
    );
}

#[test]
fn comparator_precondition_names_unbounded_signal() {
    let source = "pragma circom 2.2.3; \
         template LessThan(n) {assert(n <= 252); signal input in[2]; \
         signal output out; out <== in[0];} \
         template Check(n) {signal input a; signal output lta; \
         lta <== LessThan(252)([a, 2**n]);} component main = Check(2);";
    let input = fixture("comparator-unbounded-signal", source);
    let result = run(&input.path(), &[], "comparator-unbounded-signal");
    let messages: Vec<_> = result.sarif["runs"][0]["results"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|entry| entry["ruleId"] == "CS0025")
        .filter_map(|entry| entry["message"]["text"].as_str())
        .collect();
    assert_eq!(messages, ["Failed to prove that `a` is constrained to be 252 bits."]);
    assert!(
        result.stdout.contains("This input to `LessThan` may not be properly constrained."),
        "{}",
        result.stdout
    );
    let compound = fixture("comparator-unbounded-expression", &source.replace("[a,", "[a + 1,"));
    let result = run(&compound.path(), &[], "comparator-unbounded-expression");
    let messages: Vec<_> = result.sarif["runs"][0]["results"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|entry| entry["ruleId"] == "CS0025")
        .filter_map(|entry| entry["message"]["text"].as_str())
        .collect();
    assert_eq!(messages, ["Failed to prove that this input is constrained to be 252 bits."]);
}

#[test]
fn comparator_width_from_complete_compile_time_function_is_analyzed() {
    let input = fixture(
        "comparator-function-width",
        "pragma circom 2.2.3; \
         function log2Ceil(a) {var n=a-1; var r=0; while(n>0) {r++; n \\= 2;} return r;} \
         template LessThan(n) {signal input in[2]; signal output out; out <== in[0];} \
         template Check(max) {signal input length; signal output y; \
         y <== LessThan(log2Ceil(max+1))([length,max+1]);} \
         component main = Check(5);",
    );
    let result = run(&input.path(), &[], "comparator-function-width");
    assert!(ids(&result.sarif).contains("CS0025"), "{}", result.stdout);
    assert!(
        result.stdout.contains("Failed to prove that `length` is constrained to be 3 bits."),
        "{}",
        result.stdout
    );
}

#[test]
fn concrete_main_arguments_reach_numeric_rules() {
    let input = fixture(
        "main-argument",
        "pragma circom 2.2.3;\n\
        template Main(n){signal output out; if(n){out<==1;}else{out<==0;}}\n\
        component main=Main(1);\n",
    );
    let path = input.path();
    let CliRun { stdout, sarif, .. } = run(&path, &[], "main-argument");
    assert!(ids(&sarif).contains("CS0009"), "{stdout}");
}

#[test]
fn resolved_main_argument_does_not_create_an_internal_error() {
    let input = fixture(
        "resolved-main-argument",
        "pragma circom 2.2.3;\n\
        function Seed(){return 1;}\n\
        template Main(n){signal output out; if(1){out<==n;}else{out<==0;}}\n\
        component main=Main(Seed());\n",
    );
    let CliRun { stdout, sarif, .. } = run(&input.path(), &[], "resolved-main-argument");
    assert!(ids(&sarif).contains("CS0009"), "{stdout}");
    assert!(!ids(&sarif).contains("T3001"), "{stdout}");
}

#[test]
fn unresolved_main_argument_is_a_source_error_without_an_internal_error() {
    let input = fixture(
        "unresolved-main-argument",
        "pragma circom 2.2.3;\n\
        template Main(n){signal output out; out<==n;}\n\
        component main=Main(MissingParameter());\n",
    );
    let CliRun { status, stdout, sarif, .. } =
        run(&input.path(), &["--level", "error"], "unresolved-main-argument");
    assert_eq!(status.code(), Some(1), "{stdout}");
    assert_eq!(ids(&sarif), BTreeSet::from(["CS0019"]), "{stdout}");
    assert_eq!(sarif["runs"][0]["results"].as_array().unwrap().len(), 1);
    assert!(stdout.contains("MissingParameter"), "{stdout}");
}

#[test]
fn directory_inputs_preserve_root_diagnostics_and_skip_non_circom_files() {
    let input = fixture(
        "directory",
        "pragma circom 2.2.3; template Root(){component c=Missing();} \
            component main=Root();",
    );
    let path = input.path();
    fs::create_dir_all(path.parent().unwrap().join("nested")).unwrap();
    fs::write(
        path.parent().unwrap().join("nested/child.circom"),
        "pragma circom 2.2.3; template Nested(){component c=OtherMissing();} \
         component main=Nested();",
    )
    .unwrap();
    fs::write(path.with_file_name("notes.txt"), "invalid text").unwrap();
    let CliRun { status, stdout, sarif, .. } =
        run(path.parent().unwrap(), &["--level", "error"], "directory");
    assert_eq!(status.code(), Some(1), "{stdout}");
    assert_eq!(ids(&sarif), BTreeSet::from(["CS0019"]));
    assert_eq!(sarif["runs"][0]["results"].as_array().unwrap().len(), 2);
    assert!(stdout.contains("analyzing template 'Root'"));
    assert!(stdout.contains("analyzing template 'Nested'"));
}

#[test]
fn repeated_runs_preserve_exact_sarif_order_and_source_spans() {
    let input = fixture(
        "repeat",
        "pragma circom 2.2.3;\n\
        template First(){component c=Missing();}\n\
        template Second(){component c=Other();} component main=First();\n",
    );
    let path = input.path();
    let CliRun { stdout: first_stdout, sarif: first, .. } = run(&path, &[], "repeat");
    let CliRun { stdout: second_stdout, sarif: second, .. } = run(&path, &[], "repeat");
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
    let input = fixture(
        "curve",
        "pragma circom 2.2.3;\n\
        template Main(){signal output out;out<==18446744069414584320+1;}\n\
        component main=Main();\n",
    );
    let path = input.path();
    let CliRun { sarif: bn254, .. } =
        run(&path, &["--curve", "BN254", "--level", "info"], "curve-bn254");
    let CliRun { sarif: gold, .. } =
        run(&path, &["--curve", "GOLDILOCKS", "--level", "info"], "curve-gold");
    assert!(!ids(&bn254).contains("CS0004"));
    assert!(ids(&gold).contains("CS0004"));
}

#[test]
fn unactionable_notices_from_multiple_callers_are_suppressed() {
    let input = fixture(
        "contexts",
        "pragma circom 2.2.3;\n\
        template Child(){signal input x;signal output y;y<--x*x;y===x*x;}\n\
        template Main(){component a=Child();a.x<==1;component b=Child();b.x<==2;}\n\
        component main=Main();\n",
    );
    let path = input.path();
    let CliRun { stdout, sarif, .. } = run(&path, &["-l", "INFO"], "contexts");
    assert!(!ids(&sarif).contains("CS0020"), "{stdout}");
    assert!(!stdout.contains("could not be certified"));
}

#[test]
fn source_errors_do_not_create_redundant_coverage_notices() {
    let input =
        fixture("incomplete-labels", "pragma circom 2.2.3;\ntemplate Broken(){\nvar value=;\n}\n");
    let result = run(&input.path(), &["-l", "INFO"], "incomplete-labels");
    assert_eq!(ids(&result.sarif), BTreeSet::from(["P1000"]), "{}", result.stdout);
    assert_eq!(result.status.code(), Some(1));
    assert!(result.stdout.contains("source error"));
}

#[test]
fn library_roots_are_independent_of_declaration_order() {
    let child = "template Child(n){signal output y;if(n){y<==1;}else{y<==0;}}";
    let wrapper = "template Wrapper(){component child=Child(1);}";
    for (name, declarations) in [
        ("library-child-first", format!("{child}\n{wrapper}")),
        ("library-wrapper-first", format!("{wrapper}\n{child}")),
    ] {
        let input = fixture(name, &format!("pragma circom 2.2.3;\n{declarations}\n"));
        let path = input.path();
        let CliRun { stdout, sarif, .. } = run(&path, &["-l", "INFO"], name);
        let results = sarif["runs"][0]["results"].as_array().unwrap();
        assert!(results.iter().any(|result| result["ruleId"] == "CS0009"), "{stdout}");
        let symbolic_child = results.iter().any(|result| {
            if result["ruleId"] != "CS0020" {
                return false;
            }
            let related = result["relatedLocations"].as_array().unwrap();
            let messages: Vec<_> =
                related.iter().map(|label| label["message"]["text"].as_str().unwrap()).collect();
            messages.iter().any(|message| message.contains("the unknown parameter `n`"))
                && messages.iter().all(|message| !message.contains("Reached through this call"))
        });
        assert!(symbolic_child, "independent symbolic Child root missing: {stdout}");
    }
}

#[test]
fn failed_sarif_write_returns_a_visible_error_and_failure_exit() {
    let input = fixture("bad-sarif", "pragma circom 2.2.3;template Main(){}");
    let path = input.path();
    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .arg(&path)
        .args(["--level", "error", "--allow", "T3001", "--sarif-file"])
        .arg(path.parent().unwrap())
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("Cannot write SARIF"), "{stdout}");
    assert!(!stdout.contains("No findings reported"));
}

#[test]
fn empty_sarif_is_written_without_a_result_written_status() {
    let input = fixture("empty-sarif", "pragma circom 2.2.3;template Main(){}");
    let path = input.path();
    let CliRun { status, stdout, sarif, .. } = run(&path, &[], "empty-sarif");
    assert_eq!(status.code(), Some(0), "{stdout}");
    assert_eq!(sarif["runs"][0]["results"].as_array().unwrap().len(), 0);
    assert!(stdout.contains("No findings reported"), "{stdout}");
    assert!(!stdout.contains("Result written"), "{stdout}");
}

#[test]
fn independent_main_files_analyze_without_a_multiple_main_error() {
    let input =
        fixture("multiple-main", "pragma circom 2.2.3; template First(){} component main=First();");
    let path = input.path();
    let other = path.with_file_name("other.circom");
    fs::write(&other, "pragma circom 2.2.3; template Second(){} component main=Second();").unwrap();
    let CliRun { stdout, sarif, .. } =
        run(path.parent().unwrap(), &["--level", "error"], "multiple-main");
    assert!(!ids(&sarif).contains("P1002"), "{stdout}");
    assert!(stdout.contains("analyzing template 'First'"), "{stdout}");
    assert!(stdout.contains("analyzing template 'Second'"), "{stdout}");
}

#[test]
fn duplicate_main_in_second_root_is_reported() {
    let input = fixture(
        "duplicate-main",
        "pragma circom 2.2.3; template First(){} component main=First();",
    );
    let path = input.path();
    let other = path.with_file_name("other.circom");
    fs::write(
        &other,
        "pragma circom 2.2.3; template Second(){} component main=Second(); component main=Second();",
    )
    .unwrap();
    let CliRun { stdout, sarif, .. } =
        run(path.parent().unwrap(), &["--level", "error"], "duplicate-main");
    assert!(ids(&sarif).contains("P1002"), "{stdout}");
}

#[test]
#[cfg(unix)]
fn sarif_file_uris_preserve_reserved_and_unicode_file_names() {
    let input = fixture("file-uri", "pragma circom 2.2.3;template Main(){Missing();}");
    let path = input.path();
    let renamed = path.with_file_name("space # % \" å.circom");
    fs::rename(path, &renamed).unwrap();
    let CliRun { status, stdout, sarif, .. } = run(&renamed, &["--level", "error"], "file-uri");
    assert_eq!(status.code(), Some(1), "{stdout}");
    assert!(stdout.contains("space # % \" å.circom"));
    let location = &sarif["runs"][0]["results"][0]["locations"][0]["physicalLocation"];
    let uri = location["artifactLocation"]["uri"].as_str().unwrap();
    assert!(uri.starts_with("file:///"), "{uri}");
    assert!(uri.ends_with("/space%20%23%20%25%20%22%20%C3%A5.circom"), "{uri}");
    assert_eq!(location["region"]["startLine"], 1);
}

#[test]
fn sarif_columns_use_declared_unicode_code_points() {
    let source = "pragma circom 2.2.3;\n/* 🦀 */ template Main(){component c=Missing();} \
        component main=Main();\n";
    let input = fixture("unicode-column", source);
    let path = input.path();
    let CliRun { sarif, .. } = run(&path, &["--level", "error"], "unicode-column");
    assert_eq!(sarif["runs"][0]["columnKind"], "unicodeCodePoints");
    let region = &sarif["runs"][0]["results"][0]["locations"][0]["physicalLocation"]["region"];
    assert_eq!(region["startLine"], 2);
    assert_eq!(region["startColumn"], 37);
    assert_eq!(region["endColumn"], 44);
}

#[test]
fn a_missing_explicit_library_file_is_reported_even_without_an_include() {
    let input = fixture("library-missing", "pragma circom 2.2.3; template Main(){}");
    let path = input.path();
    let missing = path.with_file_name("missing.circom");
    let CliRun { status, stdout, sarif, .. } = run(
        &path,
        &["--level", "error", "--library", missing.to_str().unwrap()],
        "library-missing",
    );
    assert_eq!(status.code(), Some(1), "{stdout}");
    assert!(ids(&sarif).contains("P1099"));
    assert!(stdout.contains("missing.circom"));
}

#[test]
#[cfg(unix)]
fn closed_stdout_reports_an_io_error_without_panicking() {
    use std::process::Stdio;

    let input = fixture("closed-stdout", "pragma circom 2.2.3; template Main(){}");
    let path = input.path();
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

#[test]
fn useful_context_continuations_require_info_and_follow_finding_filters() {
    let input = fixture(
        "useful-contexts",
        "pragma circom 2.2.3;\n\
        template Child(n){var x=1;if(n==1){log(x);}}\n\
        template Main(){component a=Child(0);component b=Child(-1);}\n\
        component main=Main();",
    );
    let filters = ["--allow", "CS0008", "--allow", "CS0009"];
    let default = run(&input.path(), &filters, "useful-context-default");
    let mut detailed_args = filters.to_vec();
    detailed_args.extend(["--level", "INFO"]);
    let detailed = run(&input.path(), &detailed_args, "useful-context-info");
    let mut findings = Vec::new();
    for (result, notes) in [(&default, 0), (&detailed, 1)] {
        assert_eq!(result.stdout.matches("warning: Assigned value of `x`").count(), 1);
        assert_eq!(result.stdout.matches("Additional call paths for CS0006").count(), notes);
        let reports = result.sarif["runs"][0]["results"].as_array().unwrap();
        let unused: Vec<_> = reports.iter().filter(|item| item["ruleId"] == "CS0006").collect();
        assert_eq!(unused.len(), 1);
        let labels = unused[0]["relatedLocations"].as_array().unwrap();
        assert_eq!(labels.len(), 2);
        assert!(labels
            .iter()
            .any(|label| label["message"]["text"] == "Observed for Child(n = 0)."));
        assert!(labels.iter().all(|label| label["message"]["text"]
            .as_str()
            .unwrap()
            .starts_with("Observed for Child(n = ")));
        findings.push(unused[0]);
    }
    assert_eq!(findings[0], findings[1]);
    for mut args in [filters.to_vec(), detailed_args] {
        args.extend(["--allow", "CS0006"]);
        let result = run(&input.path(), &args, "useful-context-filtered");
        assert!(!result.stdout.contains("Assigned value of `x`"));
        assert!(!result.stdout.contains("Additional call paths"));
        assert!(!ids(&result.sarif).contains("CS0006"));
    }
}
