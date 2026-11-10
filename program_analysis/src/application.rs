//! Application orchestration for the owned Circom frontend and certified rules.

mod diagnostics;
mod inputs;
mod scopes;

use std::collections::BTreeSet;
use std::io;
use std::path::PathBuf;

use parser::hir::{lift_project, DefinitionRef};
use parser::frontend::{load_sources, SourceId, Version, VersionPolicy};
use program_structure::constants::Curve;
use program_structure::file_definition::FileLibrary;
use program_structure::report::Report;

use crate::application::diagnostics::Diagnostics;
use crate::application::scopes::ScopeRunner;
use crate::interprocedural::ProjectAnalysis;
use crate::rules::{RenderError, SourceMap};

/// Source reports and completed definition analyses in deterministic source order.
pub struct AnalysisOutput {
    pub files: FileLibrary,
    pub diagnostics: Vec<Report>,
    pub scopes: Vec<AnalyzedScope>,
}

/// Reports associated with one source definition, including its concrete contexts.
pub struct AnalyzedScope {
    pub description: String,
    pub reports: Vec<Report>,
}

/// Work about to begin. Definition events include each distinct call context.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AnalysisProgress<'a> {
    LoadingSources,
    LiftingSources,
    IndexingProject,
    AnalyzingFunction(&'a str),
    AnalyzingTemplate(&'a str),
    AnalyzingBus(&'a str),
}

/// Analyze entry files and their includes using Circom 2.2.3 syntax.
///
/// Syntax and semantic failures become reports and preserve independent definitions.
///
/// # Errors
/// Returns an error for a violated source identity, location, or analysis invariant.
pub fn analyze_files(
    paths: &[PathBuf],
    libraries: &[PathBuf],
    curve: Curve,
) -> Result<AnalysisOutput, ApplicationError> {
    analyze_files_with_progress(paths, libraries, curve, |_| Ok(()))
}

/// Analyze entry files, reporting each stage before starting its work.
///
/// Reports retain the same order as [`analyze_files`]. A failed progress write stops
/// analysis immediately; it does not become a source diagnostic.
///
/// # Errors
/// Returns an error for a failed progress write or an analysis invariant violation.
pub fn analyze_files_with_progress(
    paths: &[PathBuf],
    libraries: &[PathBuf],
    curve: Curve,
    mut progress: impl FnMut(AnalysisProgress<'_>) -> io::Result<()>,
) -> Result<AnalysisOutput, ApplicationError> {
    progress(AnalysisProgress::LoadingSources)?;
    let (paths, input_reports) = inputs::expand(paths);
    let loaded = load_sources(&paths, libraries, VersionPolicy::new(Version::new(2, 2, 3)));
    let paths: BTreeSet<_> = paths.iter().filter_map(|path| path.canonicalize().ok()).collect();
    let roots: Vec<SourceId> =
        loaded.files.iter().filter(|file| paths.contains(&file.path)).map(|file| file.id).collect();
    let sources = SourceMap::from_loaded(&loaded, &roots)?;
    progress(AnalysisProgress::LiftingSources)?;
    let lifted = lift_project(&loaded);
    let mut diagnostics = Diagnostics::new(&sources);
    for report in input_reports {
        diagnostics.push(report);
    }
    for path in libraries {
        if !path.exists() && path.extension().is_some_and(|extension| extension == "circom") {
            diagnostics.push(Report::error(
                format!("Cannot read library file {}", path.display()),
                program_structure::report_code::ReportCode::ParseFail,
            ));
        }
    }
    diagnostics.frontend(&loaded, &lifted)?;
    progress(AnalysisProgress::IndexingProject)?;
    let summaries = ProjectAnalysis::build(&lifted, curve)
        .map_err(|error| ApplicationError::Invariant(format!("invalid call graph: {error:?}")))?;
    let mut runner = ScopeRunner::new(&summaries, &sources, &mut diagnostics);
    runner.analyze(&mut progress)?;
    let reports = runner.finish();
    let mut scopes = Vec::new();
    for function in lifted.hir.functions() {
        if roots.contains(&function.span.source()) {
            scopes.push(AnalyzedScope {
                description: format!("function '{}'", function.name),
                reports: reports
                    .get(&DefinitionRef::Function(function.id))
                    .cloned()
                    .unwrap_or_default(),
            });
        }
    }
    for template in lifted.hir.templates() {
        if roots.contains(&template.span.source()) {
            scopes.push(AnalyzedScope {
                description: format!("template '{}'", template.name),
                reports: reports
                    .get(&DefinitionRef::Template(template.id))
                    .cloned()
                    .unwrap_or_default(),
            });
        }
    }
    Ok(AnalysisOutput {
        files: sources.files().clone(),
        diagnostics: diagnostics.finish()?,
        scopes,
    })
}

#[derive(Debug, thiserror::Error)]
pub enum ApplicationError {
    #[error("cannot report analysis progress: {0}")]
    Progress(#[from] io::Error),
    #[error(transparent)]
    Render(#[from] RenderError),
    #[error("{0}")]
    Invariant(String),
}
