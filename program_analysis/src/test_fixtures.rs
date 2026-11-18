//! Small source fixtures shared by unit tests of port-expansion adapters.

use std::fs;
use std::sync::atomic::{AtomicUsize, Ordering};

use parser::hir::{lift_project, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};

/// Load one template with a scalar input and an output of the requested array shape.
pub(crate) fn port_project(shape: &str) -> LiftedProject {
    static NEXT_DIRECTORY: AtomicUsize = AtomicUsize::new(0);
    let sequence = NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed);
    let directory = std::env::temp_dir()
        .join(format!("circomspect-port-shape-{}-{sequence}", std::process::id()));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, format!("template T(n){{signal input x;signal output bits{shape};}}"))
        .unwrap();
    let project = lift_project(&load_sources(
        &[path],
        std::slice::from_ref(&directory),
        VersionPolicy::new(Version::new(2, 2, 3)),
    ));
    fs::remove_dir_all(directory).unwrap();
    project
}
