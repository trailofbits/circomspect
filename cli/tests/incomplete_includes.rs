#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]

use std::fs;
use std::process::Command;

#[test]
fn missing_include_preserves_independent_warning_without_false_source_error() {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-incomplete-include-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    fs::create_dir_all(&directory).unwrap();
    let entry = directory.join("entry.circom");
    fs::write(
        &entry,
        "pragma circom 2.2.3; include \"absent.circom\"; \
         template Safe(){signal input x;assert(x);} \
         template Depends(){component c=Missing();} component main=Safe();",
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .args([entry.to_str().unwrap(), "--level", "warning"])
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("cannot find included file absent.circom"), "{stdout}");
    assert!(stdout.contains("This assertion checks witness-dependent"), "{stdout}");
    assert!(!stdout.contains("unresolved Template call"), "{stdout}");
    assert!(!stdout.contains("Undefined template"), "{stdout}");
    assert_eq!(stdout.matches("error:").count(), 1, "{stdout}");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn shared_missing_include_is_reported_once_across_roots() {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-shared-missing-include-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    fs::create_dir_all(&directory).unwrap();
    fs::write(
        directory.join("shared.circom"),
        "pragma circom 2.2.3; include \"absent.circom\"; template Shared(){}",
    )
    .unwrap();
    let first = directory.join("first.circom");
    let second = directory.join("second.circom");
    fs::write(&first, "pragma circom 2.2.3; include \"shared.circom\"; component main=Shared();")
        .unwrap();
    fs::write(&second, "pragma circom 2.2.3; include \"shared.circom\"; component main=Shared();")
        .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .args([first.to_str().unwrap(), second.to_str().unwrap(), "--level", "error"])
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();

    assert!(!output.status.success(), "{stdout}");
    assert_eq!(stdout.matches("cannot find included file absent.circom").count(), 1, "{stdout}");
    assert_eq!(stdout.matches("error:").count(), 1, "{stdout}");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn shared_syntax_error_is_reported_once_across_roots() {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-shared-syntax-error-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    fs::create_dir_all(&directory).unwrap();
    fs::write(
        directory.join("shared.circom"),
        "pragma circom 2.2.3; template Shared(){var value = ;}",
    )
    .unwrap();
    fs::write(
        directory.join("first.circom"),
        "pragma circom 2.2.3; include \"shared.circom\"; component main=Shared();",
    )
    .unwrap();
    fs::write(
        directory.join("second.circom"),
        "pragma circom 2.2.3; include \"shared.circom\"; component main=Shared();",
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .args([directory.to_str().unwrap(), "--level", "error"])
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(!output.status.success(), "{stdout}");
    assert_eq!(stdout.matches("error:").count(), 1, "{stdout}");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn shared_semantic_error_is_reported_once_across_roots() {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-shared-semantic-error-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    fs::create_dir_all(&directory).unwrap();
    fs::write(
        directory.join("shared.circom"),
        "pragma circom 2.2.3; template Shared(){component child=Missing();}",
    )
    .unwrap();
    for name in ["first.circom", "second.circom"] {
        fs::write(
            directory.join(name),
            "pragma circom 2.2.3; include \"shared.circom\"; component main=Shared();",
        )
        .unwrap();
    }

    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .args([directory.to_str().unwrap(), "--level", "error"])
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(!output.status.success(), "{stdout}");
    assert_eq!(stdout.matches("error: unresolved Template call `Missing`").count(), 1, "{stdout}");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn included_root_warning_is_streamed_once() {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-included-root-warning-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    fs::create_dir_all(&directory).unwrap();
    fs::write(
        directory.join("child.circom"),
        "pragma circom 2.2.3; template Child(){signal input x; \
         signal output out; assert(x == 1); out <== x;}",
    )
    .unwrap();
    fs::write(
        directory.join("root.circom"),
        "pragma circom 2.2.3; include \"child.circom\"; \
         template Root(){signal input x; signal output out; \
         component child=Child(); child.x <== x; out <== child.out;} \
         component main=Root();",
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .arg(&directory)
        .args(["--timeout", "2"])
        .output()
        .unwrap();
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert_eq!(
        stdout.matches("warning: This assertion checks witness-dependent").count(),
        1,
        "{stdout}"
    );
    fs::remove_dir_all(directory).unwrap();
}
