use std::collections::BTreeMap;
use std::cmp::Ordering;

use parser::hir::{SemanticCode, SemanticDiagnostic, Severity};
use parser::frontend::{LoadedProject, SourceId, Span};
use program_structure::file_definition::{FileID, FileLibrary};
use program_structure::report::{MessageCategory, Report};
use program_structure::report_code::ReportCode;

use crate::interprocedural::CallContext;

use crate::rules::RuleKind;

/// Source files and their renderer IDs, created in parser source order.
pub struct SourceMap<'a> {
    files: FileLibrary,
    sources: BTreeMap<SourceId, (FileID, &'a str)>,
}

impl<'a> SourceMap<'a> {
    /// Build a map for the existing terminal and SARIF renderers.
    ///
    /// # Errors
    /// Returns an error for duplicate source identities or roots absent from the loaded project.
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

    #[must_use]
    pub fn file_id(&self, source: SourceId) -> Option<FileID> {
        self.sources.get(&source).map(|(file, _)| *file)
    }

    /// Convert a typed HIR diagnostic through the existing report renderers.
    ///
    /// # Errors
    /// Returns an error for an unknown source or an invalid UTF-8 byte span.
    pub fn semantic_report(&self, diagnostic: &SemanticDiagnostic) -> Result<Report, RenderError> {
        let (file, range) = self.location(diagnostic.span)?;
        let code = semantic_report_code(diagnostic.code);
        let mut report = match diagnostic.severity {
            Severity::Error => Report::error(diagnostic.message.clone(), code),
            Severity::Warning => Report::warning(diagnostic.message.clone(), code),
        };
        report.add_primary(range, file, diagnostic.message.clone());
        Ok(report)
    }

    pub(crate) fn location(
        &self,
        span: Span,
    ) -> Result<(FileID, std::ops::Range<usize>), RenderError> {
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

fn semantic_report_code(code: SemanticCode) -> ReportCode {
    match code {
        SemanticCode::MissingCall => ReportCode::UnresolvedCall,
        SemanticCode::WrongFunction => ReportCode::UndefinedFunction,
        SemanticCode::WrongTemplate => ReportCode::UndefinedTemplate,
        SemanticCode::DuplicateFunction => ReportCode::SameFunctionDeclaredTwice,
        SemanticCode::DuplicateTemplate => ReportCode::SameTemplateDeclaredTwice,
        SemanticCode::DuplicateSymbol => ReportCode::SameSymbolDeclaredTwice,
        SemanticCode::Shadowing => ReportCode::ShadowingVariable,
        SemanticCode::ParameterCollision => ReportCode::ParameterNameCollision,
        SemanticCode::MissingBusType => ReportCode::MissingBusType,
        SemanticCode::InvalidAssignment => ReportCode::WrongTypesInAssignOperation,
        SemanticCode::WrongBusAssignment => ReportCode::WrongBusAssignment,
        SemanticCode::WrongAssignmentExpression => ReportCode::WrongAssignmentExpression,
        SemanticCode::WrongAssignmentRank => ReportCode::WrongAssignmentRank,
        SemanticCode::InvalidCallArgument => ReportCode::InvalidArgumentInCall,
        SemanticCode::InvalidSignalAccess => ReportCode::InvalidSignalAccess,
        SemanticCode::InvalidTag => ReportCode::InvalidTag,
        SemanticCode::InputTagAccess => ReportCode::InputTagAccess,
        SemanticCode::InvalidTagAfterArray => ReportCode::InvalidTagAfterArray,
        SemanticCode::InvalidArrayAccess => ReportCode::InvalidArrayAccess,
        SemanticCode::InvalidArrayIndexDimension => ReportCode::InvalidArraySize,
        SemanticCode::InvalidArrayIndexBus => ReportCode::InvalidArrayIndexBus,
        SemanticCode::AnonymousInput => ReportCode::AnonymousComponentError,
        SemanticCode::ForbiddenDeclaration => ReportCode::ForbiddenDeclarationInFunction,
        SemanticCode::TemplateReturn => ReportCode::TemplateWithReturnStatement,
        SemanticCode::ConstraintInFunction => ReportCode::ConstraintGeneratorInFunction,
        SemanticCode::UnknownSymbol => ReportCode::NonExistentSymbol,
        SemanticCode::WrongArity => ReportCode::WrongArityUnspecified,
        SemanticCode::NonConstantArrayLength => ReportCode::NonConstantArrayLength,
        SemanticCode::NonComputableExpression => ReportCode::NonComputableExpression,
        SemanticCode::FeatureVersion => ReportCode::CompilerVersionError,
    }
}

/// A finding backed by a source location. Its report code and level are fixed
/// by `RuleKind`, so callers cannot override them.
///
/// ```compile_fail
/// use circomspect_program_analysis::rules::{Finding, RuleKind};
/// fn alter_level(finding: &mut Finding) {
///     finding.kind = RuleKind::BitwiseComplement;
/// }
/// ```
///
/// ```compile_fail
/// use circomspect_program_analysis::rules::{Finding, RuleKind};
/// use circomspect_program_analysis::interprocedural::CallContext;
/// use parser::frontend::{SourceId, Span};
/// fn forge(context: CallContext) {
///     let span = Span::checked(SourceId::new(0), 0..0, "").unwrap();
///     let _ = Finding::at(context, RuleKind::Complexity, String::new(), span, String::new());
/// }
/// ```
#[derive(Clone)]
pub struct Finding {
    context: CallContext,
    kind: RuleKind,
    message: String,
    primary: Span,
    primary_label: String,
    secondary: Vec<(Span, String)>,
}

impl Finding {
    #[must_use]
    pub(super) fn at(
        context: CallContext,
        kind: RuleKind,
        message: String,
        primary: Span,
        primary_label: String,
    ) -> Self {
        Self { context, kind, message, primary, primary_label, secondary: Vec::new() }
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

    #[must_use]
    pub fn context(&self) -> &CallContext {
        &self.context
    }

    pub(super) fn compare_output(&self, other: &Self) -> Ordering {
        let primary = (
            self.kind,
            &self.context,
            self.primary.source(),
            self.primary.start(),
            self.primary.end(),
            &self.message,
            &self.primary_label,
        )
            .cmp(&(
                other.kind,
                &other.context,
                other.primary.source(),
                other.primary.start(),
                other.primary.end(),
                &other.message,
                &other.primary_label,
            ));
        if primary != Ordering::Equal {
            return primary;
        }
        for ((left_span, left_label), (right_span, right_label)) in
            self.secondary.iter().zip(&other.secondary)
        {
            let secondary = (left_span.source(), left_span.start(), left_span.end(), left_label)
                .cmp(&(right_span.source(), right_span.start(), right_span.end(), right_label));
            if secondary != Ordering::Equal {
                return secondary;
            }
        }
        self.secondary.len().cmp(&other.secondary.len())
    }

    /// Convert a checked source span to the existing report representation.
    ///
    /// # Errors
    /// Returns an error if any label has an unknown source or an invalid UTF-8 byte span.
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

#[cfg(test)]
mod tests {
    use std::fs;

    use parser::hir::lift_project;
    use parser::frontend::{load_sources, LoadedProject, SourceId, Span, Version, VersionPolicy};
    use program_structure::report::MessageCategory;
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::build_cfg;
    use crate::interprocedural::ProjectAnalysis;
    use crate::rules::reporting::{Finding, RenderError, SourceMap};
    use crate::rules::{RuleContext, RuleKind};

    fn fixture() -> (LoadedProject, Finding) {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-report-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let root = directory.join("main.circom");
        fs::write(&root, "include \"lib.circom\"; template Check() {} // π\n").unwrap();
        fs::write(directory.join("lib.circom"), "template Library() {}\n").unwrap();
        let loaded = load_sources(&[root], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let definition = lifted.hir.definition("Check").unwrap();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let evidence = summaries.contexts().symbolic_root(definition).unwrap();
        let facts = summaries.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let context = RuleContext::new(&facts, &summaries, &evidence).unwrap();
        let primary = Span::checked(loaded.files[0].id, 22..30, &loaded.files[0].text).unwrap();
        let finding = context.finding(
            RuleKind::TooManyArguments,
            "proved property".to_string(),
            primary,
            "evidence".to_string(),
        );
        (loaded, finding)
    }

    #[test]
    fn finding_bridge_preserves_fixed_code_level_and_related_location() {
        let (loaded, finding) = fixture();
        let included = &loaded.files[1];
        let secondary = Span::checked(included.id, 0..8, &included.text).unwrap();
        let finding = finding.with_secondary(secondary, "related".to_string());
        let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
        let report = finding.to_report(&sources).unwrap();
        assert_eq!(report.id(), "CS0012");
        assert_eq!(*report.category(), MessageCategory::Warning);
        assert_eq!(report.primary()[0].range, 22..30);
        assert_eq!(report.secondary()[0].range, 0..8);
        assert_ne!(report.primary()[0].file_id, report.secondary()[0].file_id);
        assert_eq!(sources.files().user_inputs().len(), 1);
        let diagnostic = report.to_diagnostic(true);
        assert_eq!(diagnostic.code.as_deref(), Some("CS0012"));
        assert_eq!(diagnostic.labels.len(), 2);
    }

    #[test]
    fn finding_bridge_rejects_unknown_and_unchecked_spans() {
        let (loaded, finding) = fixture();
        let source = &loaded.files[0];
        let sources = SourceMap::from_loaded(&loaded, &[source.id]).unwrap();
        let unknown = Span::checked(SourceId::new(42), 0..0, "").unwrap();
        let oversized = Span::checked(source.id, 0..100, &"x".repeat(100)).unwrap();
        let pi_start = source.text.find('π').unwrap();
        let split_utf8 =
            Span::checked(source.id, pi_start..pi_start + 1, &"x".repeat(100)).unwrap();
        for (span, expected) in [
            (unknown, RenderError::UnknownSource(unknown.source())),
            (oversized, RenderError::InvalidSpan(oversized)),
            (split_utf8, RenderError::InvalidSpan(split_utf8)),
        ] {
            let forged = Finding::at(
                finding.context().clone(),
                finding.kind(),
                "test".to_string(),
                span,
                "label".to_string(),
            );
            assert_eq!(forged.to_report(&sources).err(), Some(expected));
        }
    }

    #[test]
    fn same_primary_findings_have_stable_secondary_order() {
        let (loaded, finding) = fixture();
        let secondary = Span::checked(loaded.files[1].id, 0..8, &loaded.files[1].text).unwrap();
        let mut result = crate::rules::RuleResult::default();
        result.add_finding(finding.clone().with_secondary(secondary, "z".to_string()));
        result.add_finding(finding.with_secondary(secondary, "a".to_string()));
        result.sort();
        let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
        let first = result.findings()[0].to_report(&sources).unwrap();
        let second = result.findings()[1].to_report(&sources).unwrap();
        assert_eq!(first.secondary()[0].message, "a");
        assert_eq!(second.secondary()[0].message, "z");
    }
}
