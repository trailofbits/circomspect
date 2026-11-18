// The fixture writes a temporary include tree and exercises the CLI boundary.
#![allow(clippy::expect_used, clippy::panic, clippy::unwrap_used)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use serde_json::Value;

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "circomspect-dependency-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).expect("create dependency fixture");
        Self(path)
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        if let Err(error) = fs::remove_dir_all(&self.0) {
            assert!(std::thread::panicking(), "remove dependency fixture: {error}");
        }
    }
}

fn run(entry: &Path, sarif: &Path) -> Value {
    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .arg(entry)
        .args(["--level", "error", "--timeout", "2"])
        .arg("--sarif-file")
        .arg(sarif)
        .output()
        .expect("run Circomspect");
    assert!(sarif.is_file(), "missing SARIF: {}", String::from_utf8_lossy(&output.stdout));
    serde_json::from_slice(&fs::read(sarif).expect("read SARIF")).expect("parse SARIF")
}

#[test]
fn missing_dependency_does_not_invent_unresolved_template_calls() {
    let fixture = Fixture::new();
    let entry = fixture.path("main.circom");
    let library = fixture.path("library.circom");
    let sarif = fixture.path("out.sarif");
    fs::write(
        &entry,
        "pragma circom 2.2.3; include \"library.circom\"; \
         template Main() { signal output out; component child = Imported(); \
         out <== child.out; } component main = Main();",
    )
    .expect("write entry");

    let missing = run(&entry, &sarif);
    let results = missing["runs"][0]["results"].as_array().expect("results");
    assert!(results.iter().any(|result| {
        result["message"]["text"]
            .as_str()
            .is_some_and(|message| message.contains("cannot find included file"))
    }));
    assert!(results.iter().any(|result| result["ruleId"] == "P1099"));
    assert!(results.iter().all(|result| result["ruleId"] != "CS0019"));

    fs::write(
        &library,
        "pragma circom 2.2.3; template Imported() { signal output out; out <== 1; }",
    )
    .expect("write library");
    let complete = run(&entry, &sarif);
    let results = complete["runs"][0]["results"].as_array().expect("results");
    assert!(results.iter().all(|result| result["level"] != "error"));
}

#[test]
fn missing_dependency_does_not_hide_independent_syntax_errors() {
    let fixture = Fixture::new();
    let entry = fixture.path("main.circom");
    let sarif = fixture.path("out.sarif");
    fs::write(
        &entry,
        "pragma circom 2.2.3; include \"library.circom\"; \
         template Main() { signal output out; out <== 1 + ; } component main = Main();",
    )
    .expect("write malformed entry");

    let output = run(&entry, &sarif);
    let results = output["runs"][0]["results"].as_array().expect("results");
    assert!(results.iter().any(|result| result["ruleId"] == "P1099"));
    assert!(results.iter().any(|result| result["ruleId"] == "P1000"));
}

#[test]
fn direct_library_directory_restores_warning_analysis() {
    let fixture = Fixture::new();
    let consumer = fixture.path("consumer/deep");
    let library_dir = fixture.path("pkg/circuits");
    fs::create_dir_all(&consumer).expect("create consumer directory");
    fs::create_dir_all(&library_dir).expect("create library directory");
    let entry = consumer.join("main.circom");
    fs::write(
        &entry,
        "pragma circom 2.2.3; include \"./pkg/circuits/lib.circom\"; \
         template Main() { signal input x; signal output out; \
         assert(x == 1); out <== x; } component main = Main();",
    )
    .expect("write entry");
    fs::write(
        library_dir.join("lib.circom"),
        "pragma circom 2.2.3; template Library() { signal input x; \
         signal output out; assert(x == 1); out <== x; }",
    )
    .expect("write library");

    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .arg(&entry)
        .arg("-L")
        .arg(&library_dir)
        .args(["--timeout", "2"])
        .output()
        .expect("run Circomspect");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("witness dependent values"), "{stdout}");
    assert!(!stdout.contains("cannot find included file"), "{stdout}");
}
