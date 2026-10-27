use std::fs;

use parser::frontend::{load_sources, Version, VersionPolicy};
use parser::hir::{lift_project, LiftedProject};

/// Load and lift one fixture source without requiring successful parsing or lifting.
pub(crate) fn lift_source(source: &str, suite_prefix: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "{suite_prefix}-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}
