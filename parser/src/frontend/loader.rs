use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

use crate::frontend::source::{DiagnosticKind, SourceId, Span, SyntaxDiagnostic, VersionPolicy};
use crate::frontend::ast::{Item, ParseOutcome};
use crate::frontend::parse_source;

#[derive(Clone, Debug)]
pub struct SourceFile {
    pub id: SourceId,
    pub path: PathBuf,
    pub text: String,
    pub outcome: ParseOutcome,
}

#[derive(Clone, Debug)]
pub struct LoadedProject {
    pub policy: VersionPolicy,
    pub files: Vec<SourceFile>,
    pub diagnostics: Vec<SyntaxDiagnostic>,
}

struct Loader<'a> {
    include_dirs: &'a [PathBuf],
    policy: VersionPolicy,
    project: LoadedProject,
    visited: HashSet<PathBuf>,
    active: HashSet<PathBuf>,
}

impl Loader<'_> {
    fn path_diagnostic(
        kind: DiagnosticKind,
        path: &Path,
        origin: Option<Span>,
        message: String,
    ) -> SyntaxDiagnostic {
        if let Some(span) = origin {
            SyntaxDiagnostic::new(kind, span, message)
        } else {
            SyntaxDiagnostic::at_path(kind, path.to_path_buf(), message)
        }
    }

    fn resolve_include(&self, path: &Path, name: &str) -> Result<Option<PathBuf>, Vec<PathBuf>> {
        let local = path.parent().unwrap_or_else(|| Path::new(".")).join(name);
        if local.is_file() {
            return Ok(Some(local));
        }
        let mut candidates = Vec::new();
        for directory in self.include_dirs {
            if directory.is_file() {
                if directory.file_name() == Path::new(name).file_name() {
                    candidates.push((
                        Path::new(name).components().count().saturating_sub(1),
                        directory.clone(),
                    ));
                }
                continue;
            }
            let mut suffix = Path::new(name);
            let mut removed = 0;
            loop {
                let candidate = directory.join(suffix);
                if candidate.is_file() {
                    candidates.push((removed, candidate));
                }
                let mut components = suffix.components();
                components.next();
                let remainder = components.as_path();
                if remainder.as_os_str().is_empty() {
                    break;
                }
                suffix = remainder;
                removed += 1;
            }
        }
        let Some(best) = candidates.iter().map(|(removed, _)| *removed).min() else {
            return Ok(None);
        };
        let mut matches: Vec<_> = candidates
            .into_iter()
            .filter(|(removed, _)| *removed == best)
            .filter_map(|(_, path)| path.canonicalize().ok())
            .collect();
        matches.sort();
        matches.dedup();
        if matches.len() > 1 {
            Err(matches)
        } else {
            Ok(matches.pop())
        }
    }

    fn visit(&mut self, path: &Path, origin: Option<Span>) {
        let canonical = match fs::canonicalize(path) {
            Ok(path) => path,
            Err(error) => {
                self.project.diagnostics.push(Self::path_diagnostic(
                    DiagnosticKind::FileRead,
                    path,
                    origin,
                    format!("cannot read {}: {error}", path.display()),
                ));
                return;
            }
        };
        if self.active.contains(&canonical) {
            self.project.diagnostics.push(Self::path_diagnostic(
                DiagnosticKind::CyclicInclude,
                &canonical,
                origin,
                format!("cyclic include of {}", canonical.display()),
            ));
            return;
        }
        if self.visited.contains(&canonical) {
            return;
        }
        let text = match fs::read_to_string(&canonical) {
            Ok(text) => text,
            Err(error) => {
                self.project.diagnostics.push(Self::path_diagnostic(
                    DiagnosticKind::FileRead,
                    &canonical,
                    origin,
                    format!("cannot read {}: {error}", canonical.display()),
                ));
                return;
            }
        };
        let id = SourceId::new(self.project.files.len());
        let outcome = parse_source(id, &text, self.policy);
        self.project.diagnostics.extend(outcome.diagnostics.iter().cloned());
        let includes: Vec<_> = outcome
            .ast
            .items
            .iter()
            .filter_map(|item| {
                if let Item::Include { path, span } = item {
                    Some((path.clone(), *span))
                } else {
                    None
                }
            })
            .collect();
        self.project.files.push(SourceFile { id, path: canonical.clone(), text, outcome });
        self.active.insert(canonical.clone());
        self.visited.insert(canonical.clone());
        for (name, span) in includes {
            match self.resolve_include(&canonical, &name) {
                Ok(Some(include)) => self.visit(&include, Some(span)),
                Ok(None) => self.project.diagnostics.push(SyntaxDiagnostic::new(
                    DiagnosticKind::MissingInclude,
                    span,
                    format!("cannot find included file {name}"),
                )),
                Err(matches) => self.project.diagnostics.push(SyntaxDiagnostic::new(
                    DiagnosticKind::MissingInclude,
                    span,
                    format!(
                        "ambiguous included file {name}; matches {}",
                        matches
                            .iter()
                            .map(|path| path.display().to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                )),
            }
        }
        self.active.remove(&canonical);
    }
}

/// Loads entry files and their includes in deterministic depth-first order.
#[must_use]
pub fn load_sources(
    paths: &[PathBuf],
    include_dirs: &[PathBuf],
    policy: VersionPolicy,
) -> LoadedProject {
    let mut loader = Loader {
        include_dirs,
        policy,
        project: LoadedProject { policy, files: Vec::new(), diagnostics: Vec::new() },
        visited: HashSet::new(),
        active: HashSet::new(),
    };
    for path in paths {
        loader.visit(path, None);
    }
    loader.project
}
