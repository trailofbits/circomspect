use std::collections::BTreeMap;

use parser::new_frontend::{LoadedProject, SourceId, Span};
use program_structure::file_definition::{FileID, FileLibrary};
use program_structure::report::{MessageCategory, Report};
use program_structure::report_code::ReportCode;

/// Source files and their legacy renderer IDs, created in parser source order.
pub struct SourceMap {
    files: FileLibrary,
    ids: BTreeMap<SourceId, FileID>,
}

impl SourceMap {
    /// Build a map for the existing terminal and SARIF renderers.
    #[must_use]
    pub fn from_loaded(project: &LoadedProject, roots: &[SourceId]) -> Self {
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
        Self { files, ids }
    }

    #[must_use]
    pub fn files(&self) -> &FileLibrary {
        &self.files
    }

    fn file(&self, source: SourceId) -> Result<FileID, RenderError> {
        self.ids.get(&source).copied().ok_or(RenderError::UnknownSource(source))
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
        let file = sources.file(self.primary.source())?;
        let mut report = match self.category {
            MessageCategory::Error => Report::error(self.message.clone(), self.code),
            MessageCategory::Warning => Report::warning(self.message.clone(), self.code),
            MessageCategory::Info => Report::info(self.message.clone(), self.code),
        };
        report.add_primary(
            self.primary.start()..self.primary.end(),
            file,
            self.primary_label.clone(),
        );
        for (span, label) in &self.secondary {
            let file = sources.file(span.source())?;
            report.add_secondary(span.start()..span.end(), file, Some(label.clone()));
        }
        Ok(report)
    }
}

#[cfg(test)]
pub(crate) fn render_for_test(
    findings: &[Finding],
    sources: &SourceMap,
    minimum: MessageCategory,
    allow: &[String],
    sarif_path: &std::path::Path,
) -> Result<(usize, usize), RenderError> {
    use program_structure::writers::{ReportWriter, SarifWriter, StdoutWriter};

    let reports =
        findings.iter().map(|finding| finding.to_report(sources)).collect::<Result<Vec<_>, _>>()?;
    let mut terminal = StdoutWriter::new(true)
        .add_filter(move |report: &Report| report.category() >= &minimum)
        .add_filter({
            let allow = allow.to_vec();
            move |report: &Report| !allow.contains(&report.id())
        });
    let terminal_count = terminal.write_reports(&reports, sources.files());
    let mut sarif = SarifWriter::new(sarif_path)
        .add_filter(move |report: &Report| report.category() >= &minimum)
        .add_filter({
            let allow = allow.to_vec();
            move |report: &Report| !allow.contains(&report.id())
        });
    let sarif_count = sarif.write_reports(&reports, sources.files());
    Ok((terminal_count, sarif_count))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RenderError {
    UnknownSource(SourceId),
}

#[cfg(test)]
mod tests {
    use std::fs;

    use parser::new_frontend::{load_sources, Version, VersionPolicy};
    use program_structure::report::MessageCategory;
    use program_structure::report_code::ReportCode;
    use super::{render_for_test, Finding, RenderError, SourceMap};

    #[test]
    fn maps_primary_and_secondary_sources_for_existing_renderer() {
        let directory =
            std::env::temp_dir().join(format!("circomspect-rule-map-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let first = directory.join("first.circom");
        let second = directory.join("second.circom");
        fs::write(&first, "template A() {}\n").unwrap();
        fs::write(&second, "template B() {}\n").unwrap();
        let loaded =
            load_sources(&[first, second], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let first = &loaded.files[0];
        let second = &loaded.files[1];
        let first_span = parser::new_frontend::Span::checked(first.id, 0..8, &first.text).unwrap();
        let second_span =
            parser::new_frontend::Span::checked(second.id, 0..8, &second.text).unwrap();
        let sources = SourceMap::from_loaded(&loaded, &[first.id]);
        let finding = Finding {
            code: ReportCode::TooManyArguments,
            category: MessageCategory::Warning,
            message: "eight parameters".to_string(),
            primary: first_span,
            primary_label: "definition".to_string(),
            secondary: vec![(second_span, "related definition".to_string())],
        };
        let report = finding.to_report(&sources).unwrap();
        assert_eq!(report.id(), "CS0012");
        assert_eq!(*report.category(), MessageCategory::Warning);
        assert_eq!(report.primary()[0].range, 0..8);
        assert_eq!(report.secondary()[0].range, 0..8);
        assert_ne!(report.primary()[0].file_id, report.secondary()[0].file_id);
        assert_eq!(sources.files().user_inputs().len(), 1);
        let diagnostic = report.to_diagnostic(true);
        assert_eq!(diagnostic.code.as_deref(), Some("CS0012"));
        assert_eq!(diagnostic.labels.len(), 2);
    }

    #[test]
    fn test_runner_uses_terminal_and_sarif_filters() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-rule-render-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(&source, "template Check() {}\n").unwrap();
        let loaded = load_sources(&[source], &[], VersionPolicy::new(Version::new(2, 2, 3)));
        let file = &loaded.files[0];
        let span = parser::new_frontend::Span::checked(file.id, 0..8, &file.text).unwrap();
        let sources = SourceMap::from_loaded(&loaded, &[file.id]);
        let findings = [
            Finding {
                code: ReportCode::TooManyArguments,
                category: MessageCategory::Warning,
                message: "warning finding".to_string(),
                primary: span,
                primary_label: "parameters".to_string(),
                secondary: Vec::new(),
            },
            Finding {
                code: ReportCode::FieldElementArithmetic,
                category: MessageCategory::Info,
                message: "informational finding".to_string(),
                primary: span,
                primary_label: "expression".to_string(),
                secondary: Vec::new(),
            },
        ];
        let output = directory.join("result.sarif.json");
        let count =
            render_for_test(&findings, &sources, MessageCategory::Warning, &[], &output).unwrap();
        assert_eq!(count, (1, 1));
        let sarif = fs::read_to_string(&output).unwrap();
        assert!(sarif.contains("\"ruleId\": \"CS0012\""));
        assert!(sarif.contains("\"level\": \"warning\""));
        assert!(sarif.contains("\"startLine\": 1"));
        assert!(sarif.contains("\"startColumn\": 1"));
        assert!(!sarif.contains("CS0004"));

        let count = render_for_test(
            &findings,
            &sources,
            MessageCategory::Info,
            &["CS0012".to_string()],
            &output,
        )
        .unwrap();
        assert_eq!(count, (1, 1));
        let sarif = fs::read_to_string(output).unwrap();
        assert!(sarif.contains("\"ruleId\": \"CS0004\""));
        assert!(!sarif.contains("CS0012"));
    }

    #[test]
    fn unknown_source_rejects_finding() {
        let loaded = load_sources(&[], &[], VersionPolicy::new(Version::new(2, 2, 3)));
        let sources = SourceMap::from_loaded(&loaded, &[]);
        let span =
            parser::new_frontend::Span::checked(parser::new_frontend::SourceId::new(42), 0..0, "")
                .unwrap();
        let finding = Finding {
            code: ReportCode::TooManyArguments,
            category: MessageCategory::Info,
            message: String::new(),
            primary: span,
            primary_label: String::new(),
            secondary: Vec::new(),
        };
        assert_eq!(
            finding.to_report(&sources).err(),
            Some(RenderError::UnknownSource(span.source()))
        );
    }
}
