use circomspect_parser::hir::{lower_project, CallTarget, DefinitionRef, SemanticCode, Severity};
use circomspect_parser::new_frontend::{load_sources, Version, VersionPolicy};
use std::fs;
use std::path::PathBuf;

fn lower(sources: &[(&str, &str)], version: Version) -> circomspect_parser::hir::LoweredProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-hir-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).expect("test fixture directory");
    let mut roots = Vec::new();
    for (name, text) in sources {
        let path = directory.join(name);
        fs::write(&path, text).expect("test fixture");
        roots.push(path);
    }
    let project = load_sources(&roots, &[PathBuf::from(&directory)], VersionPolicy::new(version));
    lower_project(&project)
}

#[test]
fn whole_project_resolution_keeps_independent_definitions() {
    let result = lower(
        &[
            ("a.circom", "function F() { return G(); } function Good() { return 1; }"),
            ("b.circom", "function G() { return 2; }"),
        ],
        Version::new(2, 2, 3),
    );
    assert_eq!(result.hir.functions().len(), 3);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(result.incomplete.is_empty(), "{:?}", result.incomplete);
    assert!(result.hir.functions().iter().any(|function| function.name == "Good"));
}

#[test]
fn duplicate_global_names_are_ambiguous() {
    let result = lower(
        &[
            ("a.circom", "function F() { return 1; } function Use() { return F(); }"),
            ("b.circom", "template F() {}"),
        ],
        Version::new(2, 2, 3),
    );
    assert_eq!(result.diagnostics.len(), 2);
    assert!(result.diagnostics.iter().all(|diagnostic| {
        diagnostic.code == SemanticCode::DuplicateSymbol && diagnostic.severity == Severity::Error
    }));
    let use_function =
        result.hir.functions().iter().find(|function| function.name == "Use").unwrap();
    let body = result.hir.block(use_function.body).unwrap();
    let call = result.hir.expression(body.expressions()[0]).unwrap();
    assert!(matches!(call.call_target(), Some(CallTarget::Ambiguous { .. })));
    assert!(result.hir.definition("F").is_none());
    assert_eq!(result.hir.definitions_named("F").len(), 2);
    assert!(result
        .hir
        .definitions_named("F")
        .contains(&DefinitionRef::Function(result.hir.functions()[0].id)));
}
