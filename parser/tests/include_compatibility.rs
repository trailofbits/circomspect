// Test fixtures deliberately use temporary files and fail on setup errors.
#![allow(clippy::allow_attributes, clippy::expect_used, clippy::unwrap_used)]

use std::path::{Path, PathBuf};

use circomspect_parser::frontend::{
    load_sources, DiagnosticKind, LoadedProject, Version, VersionPolicy,
};

struct Fixture(PathBuf);

impl Fixture {
    fn new(name: &str) -> Self {
        let path = std::env::temp_dir().join(format!(
            "circomspect-include-compat-{name}-{}-{:?}",
            std::process::id(),
            std::thread::current().id(),
        ));
        std::fs::create_dir_all(&path).unwrap();
        Self(path.canonicalize().unwrap())
    }

    fn write(&self, relative: &str, source: &str) -> PathBuf {
        let path = self.0.join(relative);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, source).unwrap();
        path
    }

    fn load(entry: &Path, libraries: &[PathBuf]) -> LoadedProject {
        load_sources(&[entry.to_path_buf()], libraries, VersionPolicy::new(Version::new(2, 2, 3)))
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

#[test]
fn repeated_and_cyclic_includes_visit_each_file_once() {
    let fixture = Fixture::new("cycle");
    let entry = fixture.write(
        "a.circom",
        "pragma circom 2.2.3; include \"b.circom\"; include \"b.circom\"; \
         template A(){} component main=A();",
    );
    fixture.write("b.circom", "pragma circom 2.2.3; include \"a.circom\"; template B(){}");
    let loaded = Fixture::load(&entry, &[]);
    assert_eq!(loaded.files.len(), 2);
    assert!(loaded.diagnostics.is_empty(), "{:?}", loaded.diagnostics);
}

#[test]
fn ordered_library_roots_select_first_exact_match() {
    let fixture = Fixture::new("library-order");
    let entry = fixture.write("entry.circom", "include \"pkg/shared.circom\";");
    let first = fixture.write("first/pkg/shared.circom", "template First(){}");
    fixture.write("second/pkg/shared.circom", "template Second(){}");
    let loaded = Fixture::load(&entry, &[fixture.0.join("first"), fixture.0.join("second")]);
    assert!(loaded.diagnostics.is_empty(), "{:?}", loaded.diagnostics);
    assert_eq!(loaded.files.len(), 2);
    assert_eq!(loaded.files[1].path, first);
}

#[test]
fn including_directory_precedes_library_roots() {
    let fixture = Fixture::new("local-priority");
    let entry = fixture.write("entry.circom", "include \"shared.circom\";");
    let local = fixture.write("shared.circom", "template Local(){}");
    fixture.write("library/shared.circom", "template Library(){}");
    let loaded = Fixture::load(&entry, &[fixture.0.join("library")]);
    assert_eq!(loaded.files.len(), 2);
    assert_eq!(loaded.files[1].path, local);
}

#[test]
fn library_search_does_not_strip_include_prefixes() {
    let fixture = Fixture::new("exact-path");
    let entry = fixture.write("entry.circom", "include \"pkg/shared.circom\";");
    fixture.write("library/shared.circom", "template Wrong(){}");
    let loaded = Fixture::load(&entry, &[fixture.0.join("library")]);
    assert_eq!(loaded.files.len(), 1);
    assert!(loaded
        .diagnostics
        .iter()
        .any(|diagnostic| diagnostic.kind == DiagnosticKind::MissingInclude));
}
