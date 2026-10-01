mod support;

use std::collections::BTreeSet;
use std::fs;

use circomspect_program_analysis::new_rules::{
    constraints, direct, numeric, uses, AbstentionReason, Finding, RenderError, RuleKind,
    RuleResult, ScopedAbstention, SourceMap,
};
use parser::hir::lower_project;
use parser::new_frontend::{load_sources, SourceId, Span, Version, VersionPolicy};
use program_structure::report::MessageCategory;
use program_structure::report_code::ReportCode;
use serde_json::Value;

fn load_fixture(name: &str, source: &str) -> parser::new_frontend::LoadedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-rules-{name}-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("main.circom");
    fs::write(&path, source).unwrap();
    load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)))
}

fn finding(code: ReportCode, category: MessageCategory, span: Span) -> Finding {
    Finding {
        code,
        category,
        message: "proved property".to_string(),
        primary: span,
        primary_label: "evidence".to_string(),
        secondary: Vec::new(),
    }
}

#[test]
fn new_rule_ids_have_distinct_renderer_descriptors() {
    let incomplete = RuleKind::IncompleteCoverage;
    assert_eq!(incomplete.code().id(), "CS0020");
    assert_eq!(incomplete.code().name(), "incomplete-analysis");
    assert_eq!(incomplete.category(), MessageCategory::Warning);
    let redundant = RuleKind::RedundantWitnessAssignment;
    assert_eq!(redundant.code().id(), "CS0021");
    assert_eq!(redundant.code().name(), "redundant-witness-assignment");
    assert_eq!(redundant.category(), MessageCategory::Warning);
    assert_ne!(ReportCode::UnnecessarySignalAssignment.id(), "CS0021");
    assert_eq!(RuleKind::BitwiseComplement.code().id(), "CS0004");
    assert_eq!(RuleKind::BitwiseComplement.category(), MessageCategory::Info);
    assert_eq!(RuleKind::UnconstrainedSignal.code().id(), "CA01");
    assert_eq!(ReportCode::UnderConstrainedSignal.id(), "CS0017");
}

#[test]
fn every_new_rule_kind_has_a_frozen_id_and_level() {
    use RuleKind::*;
    let expected = [
        (BitwiseComplement, "CS0004", MessageCategory::Info),
        (Bn254SpecificCircuit, "CS0016", MessageCategory::Warning),
        (ConstantConditional, "CS0009", MessageCategory::Warning),
        (FieldArithmetic, "CS0004", MessageCategory::Info),
        (FieldComparison, "CS0003", MessageCategory::Info),
        (NonstrictBinaryConversion, "CS0010", MessageCategory::Warning),
        (UnconstrainedDivision, "CS0015", MessageCategory::Warning),
        (SignalAssignment, "CS0005", MessageCategory::Warning),
        (RedundantWitnessAssignment, "CS0021", MessageCategory::Warning),
        (UnconstrainedSignal, "CA01", MessageCategory::Warning),
        (UnconstrainedLessThan, "CS0014", MessageCategory::Warning),
        (UnusedVariableValue, "CS0006", MessageCategory::Warning),
        (UnusedParameterValue, "CS0007", MessageCategory::Warning),
        (SideEffectFreeAssignment, "CS0008", MessageCategory::Warning),
        (UnusedOutputSignal, "CS0018", MessageCategory::Warning),
        (Complexity, "CS0011", MessageCategory::Warning),
        (TooManyArguments, "CS0012", MessageCategory::Warning),
        (IncompleteCoverage, "CS0020", MessageCategory::Warning),
    ];
    for (kind, id, level) in expected {
        assert_eq!(kind.code().id(), id, "{kind:?}");
        assert_eq!(kind.category(), level, "{kind:?}");
    }
}

#[test]
fn rule_families_partition_the_planned_rules() {
    let families = [numeric::KINDS, constraints::KINDS, uses::KINDS, direct::KINDS];
    let mut kinds = BTreeSet::new();
    for family in families {
        for kind in family {
            assert!(kinds.insert(*kind), "duplicate rule kind: {kind:?}");
        }
    }
    assert_eq!(kinds.len(), 17);
    assert!(!kinds.contains(&RuleKind::IncompleteCoverage));
    assert!(kinds.contains(&RuleKind::UnconstrainedSignal));
    assert!(kinds.contains(&RuleKind::UnusedVariableValue));
    assert!(kinds.contains(&RuleKind::UnusedParameterValue));
}

#[test]
fn abstention_keeps_an_unproved_predicate_out_of_reports() {
    let loaded = load_fixture("abstain", "template Check(n) { signal output y; y <-- n; }\n");
    let lowered = lower_project(&loaded);
    let definition = lowered.hir.definition("Check").unwrap();
    let source = &loaded.files[0];
    let span = Span::checked(source.id, 0..8, &source.text).unwrap();
    let sources = SourceMap::from_loaded(&loaded, &[source.id]).unwrap();
    let mut result = RuleResult::default();
    result.add_abstention(ScopedAbstention {
        definition,
        span,
        reason: AbstentionReason::SymbolicParameters,
    });
    assert!(result.findings().is_empty());
    assert_eq!(result.abstentions().len(), 1);
    let output = source.path.with_extension("sarif.json");
    assert_eq!(
        support::render(result.findings(), &sources, MessageCategory::Info, &[], &output).unwrap(),
        (0, 0)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(output).unwrap()).unwrap();
    assert_eq!(sarif["runs"][0]["results"].as_array().unwrap().len(), 0);
}

#[test]
fn source_map_preserves_primary_secondary_and_diagnostic_fields() {
    let loaded = load_fixture("locations", "include \"lib.circom\"; template Check() {}\n");
    let directory = loaded.files[0].path.parent().unwrap();
    fs::write(directory.join("lib.circom"), "template Library() {}\n").unwrap();
    let loaded = load_sources(
        &[loaded.files[0].path.clone()],
        &[directory.to_path_buf()],
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    let root = &loaded.files[0];
    let included = &loaded.files[1];
    let primary = Span::checked(root.id, 22..30, &root.text).unwrap();
    let secondary = Span::checked(included.id, 0..8, &included.text).unwrap();
    let sources = SourceMap::from_loaded(&loaded, &[root.id]).unwrap();
    let mut finding = finding(ReportCode::TooManyArguments, MessageCategory::Warning, primary);
    finding.secondary.push((secondary, "related".to_string()));
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
    let output = directory.join("locations.sarif.json");
    assert_eq!(
        support::render(&[finding], &sources, MessageCategory::Info, &[], &output).unwrap(),
        (1, 1)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(output).unwrap()).unwrap();
    let result = &sarif["runs"][0]["results"][0];
    assert_eq!(result["locations"][0]["physicalLocation"]["region"]["startColumn"], 23);
    assert_eq!(result["relatedLocations"][0]["physicalLocation"]["region"]["startColumn"], 1);
}

#[test]
fn test_runner_applies_level_allow_and_root_filters_to_both_renderers() {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-rule-render-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let root = directory.join("main.circom");
    let library = directory.join("lib.circom");
    fs::write(&root, "include \"lib.circom\"; template Check() {}\n").unwrap();
    fs::write(&library, "template Library() {}\n").unwrap();
    let loaded = load_sources(
        &[root],
        std::slice::from_ref(&directory),
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    let root = &loaded.files[0];
    let included = &loaded.files[1];
    let root_span = Span::checked(root.id, 22..30, &root.text).unwrap();
    let included_span = Span::checked(included.id, 0..8, &included.text).unwrap();
    let sources = SourceMap::from_loaded(&loaded, &[root.id]).unwrap();
    let findings = [
        finding(ReportCode::TooManyArguments, MessageCategory::Warning, root_span),
        finding(ReportCode::FieldElementArithmetic, MessageCategory::Info, root_span),
        finding(ReportCode::UnconstrainedDivision, MessageCategory::Warning, included_span),
        finding(ReportCode::UndefinedFunction, MessageCategory::Error, included_span),
    ];
    let output = directory.join("result.sarif.json");
    let count =
        support::render(&findings, &sources, MessageCategory::Warning, &[], &output).unwrap();
    assert_eq!(count, (2, 2));
    let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
    let results = sarif["runs"][0]["results"].as_array().unwrap();
    assert_eq!(results.len(), 2);
    assert_eq!(results[0]["ruleId"], "CS0012");
    assert_eq!(results[0]["level"], "warning");
    assert_eq!(results[0]["locations"][0]["physicalLocation"]["region"]["startLine"], 1);
    assert_eq!(results[0]["locations"][0]["physicalLocation"]["region"]["startColumn"], 23);
    assert_eq!(results[1]["ruleId"], "T2001");
    assert_eq!(results[1]["level"], "error");

    let count =
        support::render(&findings, &sources, MessageCategory::Info, &["CS0012"], &output).unwrap();
    assert_eq!(count, (2, 2));
    let sarif: Value = serde_json::from_str(&fs::read_to_string(output).unwrap()).unwrap();
    let results = sarif["runs"][0]["results"].as_array().unwrap();
    assert_eq!(results.len(), 2);
    assert_eq!(results[0]["ruleId"], "CS0004");
    assert_eq!(results[0]["level"], "note");
    assert_eq!(results[1]["ruleId"], "T2001");
}

#[test]
fn unknown_source_and_invalid_spans_fail_before_rendering() {
    let loaded = load_fixture("invalid-span", "template Check() { signal output π; }\n");
    let source = &loaded.files[0];
    let sources = SourceMap::from_loaded(&loaded, &[source.id]).unwrap();
    assert_eq!(
        SourceMap::from_loaded(&loaded, &[SourceId::new(42)]).err(),
        Some(RenderError::UnknownRoot(SourceId::new(42)))
    );
    let mut duplicated = loaded.clone();
    duplicated.files.push(loaded.files[0].clone());
    assert_eq!(
        SourceMap::from_loaded(&duplicated, &[source.id]).err(),
        Some(RenderError::DuplicateSource(source.id))
    );
    let unknown = Span::checked(SourceId::new(42), 0..0, "").unwrap();
    assert_eq!(
        finding(ReportCode::TooManyArguments, MessageCategory::Warning, unknown)
            .to_report(&sources)
            .err(),
        Some(RenderError::UnknownSource(unknown.source()))
    );

    let too_long = Span::checked(source.id, 0..100, &"x".repeat(100)).unwrap();
    assert_eq!(
        finding(ReportCode::TooManyArguments, MessageCategory::Warning, too_long)
            .to_report(&sources)
            .err(),
        Some(RenderError::InvalidSpan(too_long))
    );

    let pi_start = source.text.find('π').unwrap();
    let inside_pi = Span::checked(source.id, pi_start..pi_start + 1, &"x".repeat(100)).unwrap();
    assert_eq!(
        finding(ReportCode::TooManyArguments, MessageCategory::Warning, inside_pi)
            .to_report(&sources)
            .err(),
        Some(RenderError::InvalidSpan(inside_pi))
    );
}
