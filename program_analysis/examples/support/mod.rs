use parser::frontend::{parse_source, LoadedProject, SourceFile, SourceId, Version, VersionPolicy};

pub type ExampleResult = Result<(), Box<dyn std::error::Error>>;

/// Assemble one in-memory library without introducing a second analysis pipeline.
pub fn loaded(source: &str) -> LoadedProject {
    let policy = VersionPolicy::new(Version::new(2, 2, 3));
    let id = SourceId::new(0);
    let outcome = parse_source(id, source, policy);
    LoadedProject {
        policy,
        diagnostics: outcome.diagnostics.clone(),
        files: vec![SourceFile { id, path: "reading.circom".into(), text: source.into(), outcome }],
    }
}
