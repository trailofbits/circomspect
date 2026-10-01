use std::collections::BTreeMap;

use parser::new_frontend::{LoadedProject, SourceId, Span};
use program_structure::file_definition::{FileID, FileLibrary};
use program_structure::report::{MessageCategory, Report};

use super::RuleKind;

/// Source files and their legacy renderer IDs, created in parser source order.
pub struct SourceMap<'a> {
    files: FileLibrary,
    sources: BTreeMap<SourceId, (FileID, &'a str)>,
}

impl<'a> SourceMap<'a> {
    /// Build a map for the existing terminal and SARIF renderers.
    pub fn from_loaded(
        project: &'a LoadedProject,
        roots: &[SourceId],
    ) -> Result<Self, RenderError> {
        let mut files = FileLibrary::new();
        let mut sources = BTreeMap::new();
        for source in &project.files {
            if sources.contains_key(&source.id) {
                return Err(RenderError::DuplicateSource(source.id));
            }
            let file = files.add_file(
                source.path.to_string_lossy().into_owned(),
                source.text.clone(),
                roots.contains(&source.id),
            );
            sources.insert(source.id, (file, source.text.as_str()));
        }
        for root in roots {
            if !sources.contains_key(root) {
                return Err(RenderError::UnknownRoot(*root));
            }
        }
        Ok(Self { files, sources })
    }

    #[must_use]
    pub fn files(&self) -> &FileLibrary {
        &self.files
    }

    fn location(&self, span: Span) -> Result<(FileID, std::ops::Range<usize>), RenderError> {
        let (file, text) =
            self.sources.get(&span.source()).ok_or(RenderError::UnknownSource(span.source()))?;
        let range = span.start()..span.end();
        if range.start > range.end
            || range.end > text.len()
            || !text.is_char_boundary(range.start)
            || !text.is_char_boundary(range.end)
        {
            return Err(RenderError::InvalidSpan(span));
        }
        Ok((*file, range))
    }
}

/// A finding backed by a source location. Its report code and level are fixed
/// by `RuleKind`, so callers cannot override them.
///
/// ```compile_fail
/// use circomspect_program_analysis::new_rules::{Finding, RuleKind};
/// fn alter_level(finding: &mut Finding) {
///     finding.kind = RuleKind::BitwiseComplement;
/// }
/// ```
#[derive(Clone)]
pub struct Finding {
    kind: RuleKind,
    message: String,
    primary: Span,
    primary_label: String,
    secondary: Vec<(Span, String)>,
}

impl Finding {
    #[must_use]
    pub fn at(kind: RuleKind, message: String, primary: Span, primary_label: String) -> Self {
        Self { kind, message, primary, primary_label, secondary: Vec::new() }
    }

    #[must_use]
    pub fn with_secondary(mut self, span: Span, label: String) -> Self {
        self.secondary.push((span, label));
        self
    }

    #[must_use]
    pub const fn kind(&self) -> RuleKind {
        self.kind
    }

    /// Convert a checked source span to the existing report representation.
    pub fn to_report(&self, sources: &SourceMap) -> Result<Report, RenderError> {
        let (file, range) = sources.location(self.primary)?;
        let code = self.kind.code();
        let mut report = match self.kind.category() {
            MessageCategory::Error => Report::error(self.message.clone(), code),
            MessageCategory::Warning => Report::warning(self.message.clone(), code),
            MessageCategory::Info => Report::info(self.message.clone(), code),
        };
        report.add_primary(range, file, self.primary_label.clone());
        for (span, label) in &self.secondary {
            let (file, range) = sources.location(*span)?;
            report.add_secondary(range, file, Some(label.clone()));
        }
        Ok(report)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, thiserror::Error)]
pub enum RenderError {
    #[error("root source {0:?} is absent from the loaded Circom project")]
    UnknownRoot(SourceId),
    #[error("source {0:?} is absent from the loaded Circom project")]
    UnknownSource(SourceId),
    #[error("source {0:?} occurs more than once in the loaded Circom project")]
    DuplicateSource(SourceId),
    #[error("source span {0:?} is outside the loaded source text or a UTF-8 boundary")]
    InvalidSpan(Span),
}
