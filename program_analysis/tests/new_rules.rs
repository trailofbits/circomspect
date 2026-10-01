mod support;

use std::collections::BTreeSet;
use std::fs;

use circomspect_program_analysis::new_rules::{
    constraints, direct, numeric, uses, AbstentionReason, Finding, RenderError, RuleContext,
    RuleContextError, RuleKind, RuleResult, ScopedAbstention, SourceMap,
};
use circomspect_program_analysis::hir_facts::FieldContext;
use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::analyze;
use circomspect_program_analysis::interprocedural::{ArgumentValue, ProjectSummaries};
use parser::hir::lower_project;
use parser::new_frontend::{load_sources, SourceId, Span, Version, VersionPolicy};
use program_structure::report::{MessageCategory, Report};
use program_structure::report_code::ReportCode;
use program_structure::utils::constants::Curve;
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

fn finding(kind: RuleKind, span: Span) -> Finding {
    Finding::at(kind, "proved property".to_string(), span, "evidence".to_string())
}

#[test]
fn rule_context_requires_matching_certified_scope() {
    let loaded = load_fixture("rule-context", "template First() {} template Second() {}\n");
    let lowered = lower_project(&loaded);
    let first = lowered.hir.definition("First").unwrap();
    let second = lowered.hir.definition("Second").unwrap();
    let cfg = build_cfg(&lowered.hir, first).unwrap();
    let bn_field = FieldContext::for_curve(Curve::Bn254);
    let gold_field = FieldContext::for_curve(Curve::Goldilocks);
    let facts = analyze(&lowered.hir, &cfg, &bn_field, None).unwrap();
    let summaries = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let first_root = summaries.symbolic_root(first).unwrap();
    let second_root = summaries.symbolic_root(second).unwrap();
    let context = RuleContext::new(&facts, &summaries, &first_root).unwrap();
    assert_eq!(context.hir().identity(), lowered.hir.identity());
    assert_eq!(context.call_context(), first_root.context());
    assert_eq!(
        RuleContext::new(&facts, &summaries, &second_root).err(),
        Some(RuleContextError::WrongDefinition)
    );
    let gold = ProjectSummaries::build(&lowered, Curve::Goldilocks).unwrap();
    let gold_root = gold.symbolic_root(first).unwrap();
    assert_eq!(
        RuleContext::new(&facts, &gold, &gold_root).err(),
        Some(RuleContextError::WrongCurve)
    );
    let foreign_loaded = load_fixture("foreign-context", "template First() {}\n");
    let foreign = lower_project(&foreign_loaded);
    let foreign_provider = ProjectSummaries::build(&foreign, Curve::Bn254).unwrap();
    let foreign_root =
        foreign_provider.symbolic_root(foreign.hir.definition("First").unwrap()).unwrap();
    assert_eq!(
        RuleContext::new(&facts, &foreign_provider, &foreign_root).err(),
        Some(RuleContextError::ForeignProject)
    );
    let gold_facts = analyze(&lowered.hir, &cfg, &gold_field, None).unwrap();
    assert_eq!(
        RuleContext::new(&gold_facts, &summaries, &first_root).err(),
        Some(RuleContextError::WrongCurve)
    );
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
    let summaries = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let context = summaries.symbolic_context_for(definition).unwrap();
    let source = &loaded.files[0];
    let span = Span::checked(source.id, 0..8, &source.text).unwrap();
    let sources = SourceMap::from_loaded(&loaded, &[source.id]).unwrap();
    let mut result = RuleResult::default();
    result.add_abstention(ScopedAbstention {
        context,
        span,
        reason: AbstentionReason::SymbolicParameters,
    });
    assert!(result.findings().is_empty());
    assert_eq!(result.abstentions().len(), 1);
    assert_eq!(result.abstentions()[0].definition(), definition);
    let field = FieldContext::for_curve(Curve::Bn254);
    let one = summaries
        .context_for(definition, vec![ArgumentValue::Scalar(field.canonical(1.into()))])
        .unwrap();
    let two = summaries
        .context_for(definition, vec![ArgumentValue::Scalar(field.canonical(2.into()))])
        .unwrap();
    assert_ne!(one, two);
    result.add_abstention(ScopedAbstention {
        context: one,
        span,
        reason: AbstentionReason::SymbolicParameters,
    });
    result.add_abstention(ScopedAbstention {
        context: two,
        span,
        reason: AbstentionReason::SymbolicParameters,
    });
    assert_eq!(result.abstentions().len(), 3);
    assert_ne!(result.abstentions()[1].context, result.abstentions()[2].context);
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
    let finding = finding(RuleKind::TooManyArguments, primary)
        .with_secondary(secondary, "related".to_string());
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
        finding(RuleKind::TooManyArguments, root_span),
        finding(RuleKind::FieldArithmetic, root_span),
        finding(RuleKind::UnconstrainedDivision, included_span),
    ];
    let mut reports =
        findings.iter().map(|finding| finding.to_report(&sources).unwrap()).collect::<Vec<_>>();
    let included_file = reports[2].primary_file_ids()[0];
    let mut error = Report::error("missing function".to_string(), ReportCode::UndefinedFunction);
    error.add_primary(
        included_span.start()..included_span.end(),
        included_file,
        "call".to_string(),
    );
    reports.push(error);
    let output = directory.join("result.sarif.json");
    let count = support::render_reports(&reports, &sources, MessageCategory::Warning, &[], &output);
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
        support::render_reports(&reports, &sources, MessageCategory::Info, &["CS0012"], &output);
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
        finding(RuleKind::TooManyArguments, unknown).to_report(&sources).err(),
        Some(RenderError::UnknownSource(unknown.source()))
    );

    let too_long = Span::checked(source.id, 0..100, &"x".repeat(100)).unwrap();
    assert_eq!(
        finding(RuleKind::TooManyArguments, too_long).to_report(&sources).err(),
        Some(RenderError::InvalidSpan(too_long))
    );

    let pi_start = source.text.find('π').unwrap();
    let inside_pi = Span::checked(source.id, pi_start..pi_start + 1, &"x".repeat(100)).unwrap();
    assert_eq!(
        finding(RuleKind::TooManyArguments, inside_pi).to_report(&sources).err(),
        Some(RenderError::InvalidSpan(inside_pi))
    );
}
