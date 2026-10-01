use std::collections::BTreeMap;

use parser::new_frontend::{LoadedProject, SourceId, Span};
use program_structure::file_definition::{FileID, FileLibrary};
use program_structure::report::{MessageCategory, Report};
use program_structure::report_code::ReportCode;

/// Source files and their legacy renderer IDs, created in parser source order.
pub struct SourceMap<'a> {
    files: FileLibrary,
    ids: BTreeMap<SourceId, FileID>,
    project: &'a LoadedProject,
}

impl<'a> SourceMap<'a> {
    /// Build a map for the existing terminal and SARIF renderers.
    pub fn from_loaded(
        project: &'a LoadedProject,
        roots: &[SourceId],
    ) -> Result<Self, RenderError> {
        let mut files = FileLibrary::new();
        let mut ids = BTreeMap::new();
        for source in &project.files {
            let file = files.add_file(
                source.path.to_string_lossy().into_owned(),
                source.text.clone(),
                roots.contains(&source.id),
            );
            ids.insert(source.id, file);
        }
        for root in roots {
            if !ids.contains_key(root) {
                return Err(RenderError::UnknownRoot(*root));
            }
        }
        Ok(Self { files, ids, project })
    }

    #[must_use]
    pub fn files(&self) -> &FileLibrary {
        &self.files
    }

    fn location(&self, span: Span) -> Result<(FileID, std::ops::Range<usize>), RenderError> {
        let file = self
            .ids
            .get(&span.source())
            .copied()
            .ok_or(RenderError::UnknownSource(span.source()))?;
        let source = self
            .project
            .files
            .iter()
            .find(|source| source.id == span.source())
            .ok_or(RenderError::UnknownSource(span.source()))?;
        let range = span.start()..span.end();
        if range.start > range.end
            || range.end > source.text.len()
            || !source.text.is_char_boundary(range.start)
            || !source.text.is_char_boundary(range.end)
        {
            return Err(RenderError::InvalidSpan(span));
        }
        Ok((file, range))
    }
}

/// A finding backed by a source location. The rule owns its evidence decision.
#[derive(Clone)]
pub struct Finding {
    pub code: ReportCode,
    pub category: MessageCategory,
    pub message: String,
    pub primary: Span,
    pub primary_label: String,
    pub secondary: Vec<(Span, String)>,
}

impl Finding {
    /// Convert a checked source span to the existing report representation.
    pub fn to_report(&self, sources: &SourceMap) -> Result<Report, RenderError> {
        let (file, range) = sources.location(self.primary)?;
        let mut report = match self.category {
            MessageCategory::Error => Report::error(self.message.clone(), self.code),
            MessageCategory::Warning => Report::warning(self.message.clone(), self.code),
            MessageCategory::Info => Report::info(self.message.clone(), self.code),
        };
        report.add_primary(range, file, self.primary_label.clone());
        for (span, label) in &self.secondary {
            let (file, range) = sources.location(*span)?;
            report.add_secondary(range, file, Some(label.clone()));
        }
        Ok(report)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RenderError {
    UnknownRoot(SourceId),
    UnknownSource(SourceId),
    InvalidSpan(Span),
}
