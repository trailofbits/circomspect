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

    fn resolve_include(&self, path: &Path, name: &str) -> Option<PathBuf> {
        let local = path.parent().unwrap_or_else(|| Path::new(".")).join(name);
        let exact = std::iter::once(local)
            .chain(self.include_dirs.iter().map(|directory| directory.join(name)))
            .find_map(|candidate| candidate.canonicalize().ok().filter(|path| path.is_file()));
        if exact.is_some() {
            return exact;
        }

        for directory in self.include_dirs {
            let Ok(root) = directory.canonicalize() else {
                continue;
            };
            for ancestor in root.ancestors().skip(1) {
                let Ok(candidate) = ancestor.join(name).canonicalize() else {
                    continue;
                };
                if candidate.is_file() && candidate.starts_with(&root) {
                    return Some(candidate);
                }
            }
        }
        None
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
        self.visited.insert(canonical.clone());
        for (name, span) in includes {
            match self.resolve_include(&canonical, &name) {
                Some(include) => self.visit(&include, Some(span)),
                None => self.project.diagnostics.push(SyntaxDiagnostic::new(
                    DiagnosticKind::MissingInclude,
                    span,
                    format!("cannot find included file {name}"),
                )),
            }
        }
    }
}

/// Loads one compilation unit and its includes in deterministic depth-first order.
/// Independent entrypoints must be loaded in separate calls.
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
    };
    for path in paths {
        loader.visit(path, None);
    }
    loader.project
}
