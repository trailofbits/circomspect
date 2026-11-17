// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use std::path::PathBuf;
use std::process::{Command, Output};
use std::fs;

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
fn explicit_library_roots_resolve_package_prefixed_imports() {
    let root = std::env::temp_dir().join(format!(
        "circomspect-explicit-libraries-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    let first = root.join("first");
    let second = root.join("second");
    fs::create_dir_all(first.join("circuits")).unwrap();
    fs::create_dir_all(second.join("@scope/second")).unwrap();
    fs::write(first.join("circuits/a.circom"), "pragma circom 2.2.3; template A() {}\n").unwrap();
    fs::write(second.join("@scope/second/b.circom"), "pragma circom 2.2.3; template B() {}\n")
        .unwrap();
    let entry = root.join("entry.circom");
    fs::write(
        &entry,
        "pragma circom 2.2.3; include \"circuits/a.circom\"; \
         include \"@scope/second/b.circom\"; template Entry() {}\n",
    )
    .unwrap();
    let output = run(&[
        entry.to_str().unwrap(),
        "-L",
        first.to_str().unwrap(),
        "-L",
        second.to_str().unwrap(),
        "--level",
        "error",
    ]);
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(output.status.success(), "{stdout}");
    assert!(stdout.contains("analyzing template 'Entry'"), "{stdout}");
}

#[test]
fn nonexistent_library_root_is_reported() {
    let entry = fixture("library_item.circom");
    let absent = entry.with_file_name("missing-package");
    let output = run(&[entry.to_str().unwrap(), "-L", absent.to_str().unwrap()]);
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("Cannot read library path"), "{stdout}");
}

#[test]
fn first_exactly_matching_library_root_wins() {
    let root = std::env::temp_dir().join(format!(
        "circomspect-ambiguous-libraries-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    let first = root.join("first/pkg/circuits");
    let second = root.join("second/pkg/circuits");
    fs::create_dir_all(&first).unwrap();
    fs::create_dir_all(&second).unwrap();
    fs::write(first.join("shared.circom"), "template Pick(){}\n").unwrap();
    fs::write(second.join("shared.circom"), "template Other(){}\n").unwrap();
    let entry = root.join("entry.circom");
    fs::write(
        &entry,
        "pragma circom 2.2.3; include \"pkg/circuits/shared.circom\"; \
         template Entry(){component p=Pick();} component main=Entry();",
    )
    .unwrap();
    let output = run(&[
        entry.to_str().unwrap(),
        "-L",
        root.join("first").to_str().unwrap(),
        "-L",
        root.join("second").to_str().unwrap(),
        "--level",
        "error",
    ]);
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(output.status.success(), "{stdout}");
    assert!(!stdout.contains("included file"), "{stdout}");
}

#[test]
fn library_without_main_is_analyzed() {
    let path = fixture("library_item.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8")]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(output.status.success(), "{stdout}");
    assert!(stdout.contains("analyzing template 'LibraryItem'"), "{stdout}");
    assert!(stdout.contains("No findings reported."), "{stdout}");
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
    assert!(!stdout.contains("Some checks"), "{stdout}");
    assert!(stdout.contains("2 source errors reported."), "{stdout}");
    assert!(stdout.contains("parsing continued"), "{stdout}");
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
fn empty_hex_literal_reports_error_without_crashing() {
    let path = fixture("empty_hex_library.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8")]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");
    let stderr = String::from_utf8(output.stderr).expect("CLI stderr is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("empty_hex_library.circom:4:"), "{stdout}");
    assert!(stdout.contains("analyzing template 'AfterInvalidHex'"), "{stdout}");
    assert!(!stderr.contains("panicked"), "{stderr}");
}

#[test]
fn oversized_version_reports_error_without_crashing() {
    let path = fixture("oversized_version.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8")]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");
    let stderr = String::from_utf8(output.stderr).expect("CLI stderr is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("error:"), "{stdout}");
    assert!(stdout.contains("oversized_version.circom:1:"), "{stdout}");
    assert!(!stderr.contains("panicked"), "{stderr}");
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
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("unexpected end of Circom source"), "{stdout}");
    assert!(stdout.contains("unclosed_definition.circom:4:19"), "{stdout}");
    assert!(stdout.contains("analyzing template 'AfterUnclosed'"), "{stdout}");
    assert!(!stdout.contains("analyzing template 'Unclosed'"), "{stdout}");
}

#[test]
fn unclosed_comment_does_not_hide_preceding_definition() {
    let path = fixture("unclosed_comment_library.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("unterminated block comment"), "{stdout}");
    assert!(stdout.contains("unclosed_comment_library.circom:9:1"), "{stdout}");
    assert!(stdout.contains("analyzing template 'BeforeComment'"), "{stdout}");
    assert!(!stdout.contains("analyzing template 'HiddenByComment'"), "{stdout}");
}

#[test]
fn unclosed_comment_inside_definition_reports_both_syntax_errors() {
    let path = fixture("unclosed_comment_in_definition.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("unterminated block comment"), "{stdout}");
    assert_eq!(stdout.matches("error:").count(), 2, "{stdout}");
    assert!(stdout.contains("analyzing template 'BeforeBrokenComment'"), "{stdout}");
    assert!(!stdout.contains("analyzing template 'BrokenByComment'"), "{stdout}");
}

#[test]
fn comment_markers_inside_include_path_are_not_comments() {
    let path = fixture("comment_in_include.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(output.status.success(), "{stdout}");
    assert!(stdout.contains("analyzing template 'UsesIncluded'"), "{stdout}");
    assert!(stdout.contains("No findings reported."), "{stdout}");
}

#[test]
fn malformed_pragma_does_not_hide_later_definition() {
    let path = fixture("malformed_pragma_library.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("malformed_pragma_library.circom"), "{stdout}");
    assert!(stdout.contains("analyzing template 'AfterMalformedPragma'"), "{stdout}");
}

#[test]
fn malformed_include_does_not_hide_later_definition() {
    let path = fixture("malformed_include_library.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("malformed_include_library.circom"), "{stdout}");
    assert!(stdout.contains("analyzing template 'AfterMalformedInclude'"), "{stdout}");
}

#[test]
fn malformed_version_value_is_located_and_later_definition_is_analyzed() {
    let path = fixture("malformed_version_value_library.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("malformed_version_value_library.circom:1:15"), "{stdout}");
    assert!(stdout.contains("analyzing template 'AfterMalformedVersionValue'"), "{stdout}");
}

#[test]
fn malformed_include_path_is_located_and_later_definition_is_analyzed() {
    let path = fixture("malformed_include_path_library.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("malformed_include_path_library.circom:2:9"), "{stdout}");
    assert!(stdout.contains("analyzing template 'AfterMalformedIncludePath'"), "{stdout}");
}

#[test]
fn missing_input_file_is_visible() {
    let path = std::env::temp_dir()
        .join(format!("circomspect-nonexistent-input-{}.circom", std::process::id()));
    let output = run(&[path.to_str().expect("temporary path is not UTF-8")]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("cannot read"), "{stdout}");
    assert!(!stdout.contains("No findings reported."), "{stdout}");
}

#[test]
fn unsupported_version_is_visible() {
    let path = fixture("unsupported_version.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8")]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("requires Circom 2.3.0"), "{stdout}");
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
fn unresolved_calls_in_mainless_library_have_incomplete_coverage() {
    let path = fixture("unresolved_library.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "info"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("Some checks need additional context"), "{stdout}");
    assert!(!stdout.contains("error:"), "{stdout}");
}

#[test]
fn unresolved_main_template_is_reported() {
    let path = fixture("unresolved_main.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("MissingMain"), "{stdout}");
    assert!(stdout.contains("MissingParameter"), "{stdout}");
    assert_eq!(stdout.matches("error:").count(), 2, "{stdout}");
    assert!(stdout.contains("unresolved_main.circom:3:"), "{stdout}");
}

#[test]
fn function_cannot_be_used_as_main_template() {
    let path = fixture("function_as_main.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("OnlyFunction"), "{stdout}");
    assert!(stdout.contains("expected Template"), "{stdout}");
    assert!(stdout.contains("function_as_main.circom:7:"), "{stdout}");
}

#[test]
fn component_initializer_requires_template_but_parameters_can_call_functions() {
    let path = fixture("function_as_component.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert_eq!(stdout.matches("error:").count(), 2, "{stdout}");
    assert!(stdout.contains("OnlyFunction"), "{stdout}");
    assert!(stdout.contains("expected Template"), "{stdout}");
    assert!(stdout.contains("function_as_component.circom:17:"), "{stdout}");
    assert!(stdout.contains("analyzing template 'UsesValidTargets'"), "{stdout}");
    assert!(stdout.contains("analyzing template 'UsesParallelWrongTarget'"), "{stdout}");
}

#[test]
fn later_component_assignments_require_templates_with_scoped_names() {
    let path = fixture("function_as_later_component.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert_eq!(stdout.matches("error:").count(), 2, "{stdout}");
    assert!(stdout.contains("function_as_later_component.circom:18:"), "{stdout}");
    assert!(stdout.contains("function_as_later_component.circom:23:"), "{stdout}");
    assert!(stdout.contains("analyzing template 'UsesValidTarget'"), "{stdout}");
    assert!(stdout.contains("analyzing template 'ScopedVarCall'"), "{stdout}");
}

#[test]
fn wrong_main_target_has_a_source_location_in_sarif() {
    let source = fixture("function_as_main.circom");
    let sarif = std::env::temp_dir().join(format!("circomspect-main-{}.sarif", std::process::id()));
    let output = run(&[
        source.to_str().expect("fixture path is not UTF-8"),
        "--level",
        "error",
        "--sarif-file",
        sarif.to_str().expect("temporary path is not UTF-8"),
    ]);
    let contents = std::fs::read_to_string(&sarif).expect("SARIF file was not written");
    std::fs::remove_file(&sarif).expect("failed to remove SARIF file");
    let sarif: serde_json::Value = serde_json::from_str(&contents).expect("invalid SARIF JSON");
    let results = sarif["runs"][0]["results"].as_array().expect("SARIF results missing");

    assert!(!output.status.success());
    assert!(results.iter().any(|result| {
        result["ruleId"] == "T2002"
            && result["locations"][0]["physicalLocation"]["region"]["startLine"] == 7
    }));
}

#[test]
fn parallel_function_cannot_be_used_as_main_template() {
    let path = fixture("parallel_function_as_main.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("expected Template"), "{stdout}");
    assert!(stdout.contains("parallel_function_as_main.circom:7:"), "{stdout}");
}

#[test]
fn valid_main_template_has_no_target_error() {
    let path = fixture("valid_main.circom");
    let output = run(&[path.to_str().expect("fixture path is not UTF-8"), "--level", "error"]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(output.status.success(), "{stdout}");
    assert!(stdout.contains("No findings reported."), "{stdout}");
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
fn calls_resolve_against_explicit_library_directory() {
    let source = fixture("consumer/library_consumer.circom");
    let library = fixture("resolved_library.circom");
    let output = run(&[
        source.to_str().expect("fixture path is not UTF-8"),
        "--library",
        library.parent().unwrap().to_str().expect("fixture path is not UTF-8"),
        "--level",
        "error",
    ]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(output.status.success(), "{stdout}");
    assert!(stdout.contains("analyzing template 'UsesLoadedLibrary'"), "{stdout}");
}

#[test]
fn syntax_errors_remain_visible_when_other_library_calls_need_context() {
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
    assert!(!stdout.contains("error: unresolved Function"), "{stdout}");
    assert!(!stdout.contains("error: unresolved Template"), "{stdout}");
}

#[test]
fn unversioned_included_library_does_not_add_a_warning_to_input() {
    let source = fixture("consumer/includes_unversioned.circom");
    let library = fixture("unversioned_library.circom");
    let output = run(&[
        source.to_str().expect("fixture path is not UTF-8"),
        "--library",
        library.parent().unwrap().to_str().expect("fixture path is not UTF-8"),
    ]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!stdout.contains("error:"), "{stdout}");
    assert!(!stdout.contains("No compiler version is specified"), "{stdout}");
}

#[test]
fn unversioned_user_input_still_has_a_warning() {
    let source = fixture("unversioned_library.circom");
    let output = run(&[source.to_str().expect("fixture path is not UTF-8")]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("No compiler version is specified"), "{stdout}");
}

#[test]
fn syntax_error_in_included_library_is_visible() {
    let source = fixture("consumer/includes_broken.circom");
    let library = fixture("broken_library.circom");
    let library_root = library.parent().expect("library has parent");
    let output = run(&[
        source.to_str().expect("fixture path is not UTF-8"),
        "--library",
        library_root.to_str().expect("fixture path is not UTF-8"),
    ]);
    let stdout = String::from_utf8(output.stdout).expect("CLI output is not UTF-8");

    assert!(!output.status.success(), "{stdout}");
    assert!(stdout.contains("error:"), "{stdout}");
    assert!(stdout.contains("broken_library.circom"), "{stdout}");
    assert!(stdout.contains("analyzing template 'IntactDefinition'"), "{stdout}");
}
