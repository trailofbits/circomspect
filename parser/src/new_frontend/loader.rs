use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};

use super::ast::{
    DiagnosticKind, ParseOutcome, SourceId, Span, SyntaxDiagnostic, SyntaxKind, VersionPolicy,
};
use super::parse_source;

#[derive(Clone, Debug)]
pub struct SourceFile {
    pub id: SourceId,
    pub path: PathBuf,
    pub text: String,
    pub outcome: ParseOutcome,
}

#[derive(Clone, Debug, Default)]
pub struct LoadedProject {
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
    fn resolve_include(&self, path: &Path, name: &str) -> Option<PathBuf> {
        let local = path.parent().unwrap_or_else(|| Path::new(".")).join(name);
        if local.is_file() {
            return Some(local);
        }
        for directory in self.include_dirs {
            let candidate = directory.join(name);
            if candidate.is_file() {
                return Some(candidate);
            }
        }
        None
    }

    fn visit(&mut self, path: &Path, origin: Option<Span>) {
        let canonical = match fs::canonicalize(path) {
            Ok(path) => path,
            Err(error) => {
                self.project.diagnostics.push(SyntaxDiagnostic::new(
                    DiagnosticKind::FileRead,
                    origin.unwrap_or_else(|| Span::from_lexer(SourceId::new(0), 0, 0)),
                    format!("cannot read {}: {error}", path.display()),
                ));
                return;
            }
        };
        if self.active.contains(&canonical) {
            self.project.diagnostics.push(SyntaxDiagnostic::new(
                DiagnosticKind::CyclicInclude,
                origin.unwrap_or_else(|| Span::from_lexer(SourceId::new(0), 0, 0)),
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
                self.project.diagnostics.push(SyntaxDiagnostic::new(
                    DiagnosticKind::FileRead,
                    origin.unwrap_or_else(|| Span::from_lexer(SourceId::new(0), 0, 0)),
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
                if item.kind == SyntaxKind::Include {
                    item.text.as_deref().map(|text| (text.to_owned(), item.span))
                } else {
                    None
                }
            })
            .collect();
        self.project.files.push(SourceFile { id, path: canonical.clone(), text, outcome });
        self.active.insert(canonical.clone());
        self.visited.insert(canonical.clone());
        for (name, span) in includes {
            if let Some(include) = self.resolve_include(&canonical, &name) {
                self.visit(&include, Some(span));
            } else {
                self.project.diagnostics.push(SyntaxDiagnostic::new(
                    DiagnosticKind::MissingInclude,
                    span,
                    format!("cannot find included file {name}"),
                ));
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
        project: LoadedProject::default(),
        visited: HashSet::new(),
        active: HashSet::new(),
    };
    for path in paths {
        loader.visit(path, None);
    }
    loader.project
}
