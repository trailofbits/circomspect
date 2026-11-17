//! Application orchestration for the owned Circom frontend and certified rules.

mod coverage;
mod diagnostics;
mod grouping;
mod inputs;
mod observer;
mod scopes;
mod units;

use std::io;
use std::path::PathBuf;
use abstract_interpretation::timeout::Timeout;

use parser::hir::{lift_project, DefinitionRef};
use program_structure::constants::Curve;
use program_structure::file_definition::FileLibrary;
use program_structure::report::Report;
use program_structure::writers::ReportWriteError;

pub use crate::application::observer::AnalysisObserver;
pub use abstract_interpretation::timeout::Timeout as AnalysisTimeout;

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

struct AnalysisSettings {
    curve: Curve,
    timeout: AnalysisTimeout,
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
    analyze_files_with_observer(paths, libraries, curve, Timeout::Unlimited, &mut progress)
}

/// Analyze files and publish diagnostics as independent scopes complete.
///
/// Final reports retain source order, proof locations, and useful call-context qualifications.
/// Coverage notices wait until their causes and affected checks are aggregated.
///
/// # Errors
/// Returns an observer output failure or an analysis invariant violation.
pub fn analyze_files_with_observer(
    paths: &[PathBuf],
    libraries: &[PathBuf],
    curve: Curve,
    timeout: AnalysisTimeout,
    observer: &mut dyn AnalysisObserver,
) -> Result<AnalysisOutput, ApplicationError> {
    observer.progress(AnalysisProgress::LoadingSources)?;
    let (paths, input_reports) = inputs::expand(paths);
    let paths = units::distinct_paths(paths);
    let (files, file_ids) = units::catalog(&paths, libraries)?;
    let settings = AnalysisSettings { curve, timeout };
    let mut pre_reports = input_reports;
    for path in libraries {
        if !path.exists() {
            pre_reports.push(Report::error(
                format!("Cannot read library path {}", path.display()),
                program_structure::report_code::ReportCode::ParseFail,
            ));
        }
    }
    let mut all_diagnostics = Vec::new();
    let mut all_scopes = Vec::new();
    let roots: Vec<_> =
        if paths.is_empty() { vec![None] } else { paths.iter().map(Some).collect() };
    for root in roots {
        let unit = units::load(root, libraries);
        let roots = unit.roots();
        let sources = SourceMap::from_shared_files(&unit.loaded, &roots, files.clone(), &file_ids)?;
        let (diagnostics, scopes) =
            analyze_unit(&unit, &sources, std::mem::take(&mut pre_reports), &settings, observer)?;
        all_diagnostics.extend(diagnostics);
        all_scopes.extend(scopes);
    }
    Ok(AnalysisOutput {
        files: files.as_ref().clone(),
        diagnostics: all_diagnostics,
        scopes: all_scopes,
    })
}

fn analyze_unit(
    unit: &units::Unit,
    sources: &SourceMap<'_>,
    pre_reports: Vec<Report>,
    settings: &AnalysisSettings,
    observer: &mut dyn AnalysisObserver,
) -> Result<(Vec<Report>, Vec<AnalyzedScope>), ApplicationError> {
    observer.progress(AnalysisProgress::LiftingSources)?;
    let loaded = &unit.loaded;
    let roots = unit.roots();
    let lifted = lift_project(loaded);
    let mut diagnostics = Diagnostics::new(sources);
    for report in pre_reports {
        diagnostics.push(report);
    }
    diagnostics.frontend(loaded, &lifted, unit.open_namespace())?;
    diagnostics.emit_new(observer)?;
    observer.progress(AnalysisProgress::IndexingProject)?;
    let summaries = ProjectAnalysis::build(&lifted, settings.curve.clone())
        .map_err(|error| ApplicationError::Invariant(format!("invalid call graph: {error:?}")))?;
    let mut runner = ScopeRunner::new(&summaries, sources, &mut diagnostics, settings.timeout);
    runner.analyze(observer)?;
    let reports = runner.finish(observer)?;
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
    Ok((diagnostics.finish(observer)?, scopes))
}

#[derive(Debug, thiserror::Error)]
pub enum ApplicationError {
    #[error("cannot report analysis progress: {0}")]
    Progress(#[from] io::Error),
    #[error(transparent)]
    Output(#[from] ReportWriteError),
    #[error(transparent)]
    Render(#[from] RenderError),
    #[error("{0}")]
    Invariant(String),
}
