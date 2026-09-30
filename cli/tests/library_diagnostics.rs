use std::path::PathBuf;
use std::process::{Command, Output};

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name)
}

fn run(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_circomspect"))
        .args(args)
        .output()
        .expect("failed to run circomspect")
}

#[test]
fn library_without_main_is_analyzed() {
    let path = fixture("library_item.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8")]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(output.status.success(), "{stdout}");
    assert!(stdout.contains("analyzing template 'LibraryItem'"), "{stdout}");
    assert!(stdout.contains("No issues found."), "{stdout}");
}

#[test]
fn syntax_error_in_one_file_does_not_hide_another_library_definition() {
    let valid = fixture("library_item.circom");
    let invalid = fixture("broken_library.circom");
    let output = run(&[
        valid.to_str().expect("fixture path is not UTF-8"),
        invalid.to_str().expect("fixture path is not UTF-8"),
    ]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("error:"), "{stdout}");
    assert!(stdout.contains("broken_library.circom"), "{stdout}");
    assert!(stdout.contains("analyzing template 'LibraryItem'"), "{stdout}");
}

#[test]
fn syntax_errors_do_not_hide_valid_definitions_in_the_same_library() {
    let path = fixture("recoverable_library.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8")]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("analyzing template 'BeforeError'"), "{stdout}");
    assert!(stdout.contains("analyzing template 'BetweenErrors'"), "{stdout}");
    assert!(stdout.contains("analyzing template 'AfterError'"), "{stdout}");
    assert!(!stdout.contains("analyzing template 'BrokenFirst'"), "{stdout}");
    assert!(!stdout.contains("analyzing template 'BrokenSecond'"), "{stdout}");
    assert_eq!(stdout.matches("error:").count(), 2, "{stdout}");
}

#[test]
fn invalid_token_does_not_hide_valid_definition_in_the_same_library() {
    let path = fixture("lexical_error_library.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8")]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("lexical_error_library.circom:4:"), "{stdout}");
    assert!(stdout.contains("analyzing template 'AfterInvalidToken'"), "{stdout}");
    assert!(!stdout.contains("analyzing template 'BrokenToken'"), "{stdout}");
}

#[test]
fn syntax_error_keeps_includes_available_to_later_definitions() {
    let path = fixture("recoverable_include.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert_eq!(stdout.matches("error:").count(), 1, "{stdout}");
    assert!(stdout.contains("analyzing template 'UsesIncludedTemplate'"), "{stdout}");
    assert!(!stdout.contains("MissingTemplate"), "{stdout}");
}

#[test]
fn unclosed_definition_does_not_hide_the_next_definition() {
    let path = fixture("unclosed_definition.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8")]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("unclosed_definition.circom:6:"), "{stdout}");
    assert!(stdout.contains("analyzing template 'AfterUnclosed'"), "{stdout}");
    assert!(!stdout.contains("analyzing template 'Unclosed'"), "{stdout}");
}

#[test]
fn missing_input_file_is_visible() {
    let path = std::env::temp_dir()
        .join(format!("circomspect-nonexistent-input-{}.circom", std::process::id()));
    let output = run(&[path.to_str().expect("temporary path is not UTF-8")]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("Failed to open file"), "{stdout}");
    assert!(!stdout.contains("No issues found."), "{stdout}");
}

#[test]
fn unsupported_version_is_visible() {
    let path = fixture("unsupported_version.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8")]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("requires version 2.2.0"), "{stdout}");
    assert!(stdout.contains("analyzing template 'LibraryItem'"), "{stdout}");
}

#[test]
fn locationless_errors_are_written_to_sarif() {
    let source = fixture("unsupported_version.circom");
    let sarif =
        std::env::temp_dir().join(format!("circomspect-version-{}.sarif", std::process::id()));
    let output = run(&[
        source.to_str().expect("fixture path is not UTF-8"),
        "--sarif-file",
        sarif.to_str().expect("temporary path is not UTF-8"),
    ]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");
    let contents = std::fs::read_to_string(&sarif).expect("SARIF file was not written");
    std::fs::remove_file(&sarif).expect("failed to remove SARIF file");
    let sarif: serde_json::Value = serde_json::from_str(&contents).expect("invalid SARIF JSON");
    let results = sarif["runs"][0]["results"].as_array().expect("SARIF results missing");

    assert!(!output.status.success(), "{stdout}");
    assert!(results.iter().any(|result| result["ruleId"] == "P1003"));
}

#[test]
fn unresolved_function_and_template_calls_are_reported() {
    let path = fixture("unresolved_library.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("MissingFunction"), "{stdout}");
    assert!(stdout.contains("MissingInner"), "{stdout}");
    assert!(stdout.contains("MissingTemplate"), "{stdout}");
}

#[test]
fn calls_to_loaded_library_definitions_are_resolved() {
    let path = fixture("resolved_library.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(output.status.success(), "{stdout}");
    assert!(stdout.contains("analyzing template 'UsesKnownDefinitions'"), "{stdout}");
}

#[test]
fn calls_resolve_against_explicit_library_files() {
    let source = fixture("consumer/library_consumer.circom");
    let library = fixture("resolved_library.circom");
    let output = run(&[
        source.to_str().expect("fixture path is not UTF-8"),
        "--library",
        library.to_str().expect("fixture path is not UTF-8"),
        "--level",
        "error",
    ]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(output.status.success(), "{stdout}");
    assert!(stdout.contains("analyzing template 'UsesLoadedLibrary'"), "{stdout}");
}

#[test]
fn syntax_errors_and_unresolved_calls_both_surface_in_partial_libraries() {
    let source = fixture("unresolved_library.circom");
    let broken = fixture("broken_library.circom");
    let output = run(&[
        source.to_str().expect("fixture path is not UTF-8"),
        broken.to_str().expect("fixture path is not UTF-8"),
        "--level",
        "error",
    ]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("error:"), "{stdout}");
    assert!(stdout.contains("broken_library.circom"), "{stdout}");
    assert!(stdout.contains("MissingFunction"), "{stdout}");
    assert!(stdout.contains("MissingTemplate"), "{stdout}");
}

#[test]
fn unversioned_included_library_does_not_add_a_warning_to_input() {
    let source = fixture("consumer/includes_unversioned.circom");
    let library = fixture("unversioned_library.circom");
    let output = run(&[
        source.to_str().expect("fixture path is not UTF-8"),
        "--library",
        library.to_str().expect("fixture path is not UTF-8"),
    ]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(output.status.success(), "{stdout}");
    assert!(!stdout.contains("does not include a version pragma"), "{stdout}");
}

#[test]
fn unversioned_user_input_still_has_a_warning() {
    let source = fixture("unversioned_library.circom");
    let output = run(&[source.to_str().expect("fixture path is not UTF-8")]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("does not include a version pragma"), "{stdout}");
}

#[test]
fn syntax_error_in_included_library_is_visible() {
    let source = fixture("consumer/includes_broken.circom");
    let library = fixture("broken_library.circom");
    let output = run(&[
        source.to_str().expect("fixture path is not UTF-8"),
        "--library",
        library.to_str().expect("fixture path is not UTF-8"),
    ]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("error:"), "{stdout}");
    assert!(stdout.contains("broken_library.circom"), "{stdout}");
    assert!(stdout.contains("analyzing template 'IntactDefinition'"), "{stdout}");
}
