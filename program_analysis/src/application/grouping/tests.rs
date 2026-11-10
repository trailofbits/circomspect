use parser::frontend::{parse_source, LoadedProject, SourceFile, SourceId, Version, VersionPolicy};
use parser::hir::lift_project;
use program_structure::report::Report;
use program_structure::report_code::ReportCode;
use program_structure::utils::constants::Curve;
use program_structure::utils::sarif_conversion::ToSarif;

use crate::application::grouping::ReportGroups;
use crate::hir_cfg::build_cfg;
use crate::interprocedural::{
    CallBlocker, CallOwner, CallReachability, ContextEvidence, ProjectAnalysis,
};
use crate::rules::{RenderError, SourceMap};

fn loaded(source: &str) -> LoadedProject {
    let id = SourceId::new(0);
    let policy = VersionPolicy::new(Version::new(2, 2, 3));
    LoadedProject {
        policy,
        diagnostics: Vec::new(),
        files: vec![SourceFile {
            id,
            path: "/project/grouping.circom".into(),
            text: source.into(),
            outcome: parse_source(id, source, policy),
        }],
    }
}

fn report(message: &str) -> Report {
    let mut report = Report::warning(message.into(), ReportCode::UnusedVariableValue);
    report.add_primary(0..1, 0, "unused value".into());
    report
}

fn child_contexts(
    provider: &ProjectAnalysis<'_>,
    caller: &ContextEvidence,
) -> Vec<ContextEvidence> {
    let definition = caller.context().definition();
    let cfg = build_cfg(provider.hir(), definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, caller, None).unwrap();
    let mut children = Vec::new();
    for site in provider.graph().calls_from(CallOwner::Definition(definition)) {
        let child = match provider.graph().reachable_call(site.id(), &facts) {
            CallReachability::Reachable(call) => {
                provider.contexts().call_evidence(&call, &facts, caller)
            }
            CallReachability::Unavailable(CallBlocker::ProvisionalSite) => {
                provider.contexts().refined_function_call_evidence(site.id(), &facts, caller)
            }
            CallReachability::Unreachable | CallReachability::Unavailable(_) => {
                panic!("fixture call must be reachable")
            }
        };
        children.push(
            child.unwrap_or_else(|error| {
                panic!("fixture context {caller:?} at {site:?}: {error:?}")
            }),
        );
    }
    children
}

fn root_context(provider: &ProjectAnalysis<'_>) -> ContextEvidence {
    let root = provider.hir().definition("Root").unwrap();
    provider.contexts().symbolic_root(root).unwrap()
}

#[test]
fn sixteen_call_findings_become_one_terminal_and_sarif_result() {
    let mut source = "function Issue(n){return n;}template Root(){".to_string();
    for index in 0..16 {
        source.push_str(&format!("var value{index}=Issue({index});"));
    }
    source.push('}');
    let loaded = loaded(&source);
    let project = lift_project(&loaded);
    let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let contexts = child_contexts(&provider, &root_context(&provider));
    assert_eq!(contexts.len(), 16);
    let sources = SourceMap::from_loaded(&loaded, &[SourceId::new(0)]).unwrap();
    let mut groups = ReportGroups::default();
    for context in &contexts {
        groups.insert(report("Unused e2"), context);
    }
    let reports = groups.finish(&sources).unwrap();
    assert_eq!(reports.len(), 1);
    assert_eq!(reports[0].message(), "Unused e2");
    assert_eq!(reports[0].primary()[0].range, 0..1);
    assert_eq!(reports[0].secondary().len(), 16);
    let terminal: Vec<_> = reports.iter().map(|report| report.to_diagnostic(true)).collect();
    let sarif: Vec<_> =
        reports.iter().map(|report| report.to_sarif(sources.files()).unwrap()).collect();
    assert_eq!(terminal.len(), 1);
    assert_eq!(sarif.len(), 1);
    assert_eq!(sarif[0].related_locations.as_ref().unwrap().len(), 16);
}

#[test]
fn single_context_and_source_reports_preserve_existing_rendering() {
    let loaded = loaded("function Issue(n){return n;}template Root(){var value=Issue(1);}");
    let project = lift_project(&loaded);
    let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let root = root_context(&provider);
    let context = child_contexts(&provider, &root).remove(0);
    let sources = SourceMap::from_loaded(&loaded, &[SourceId::new(0)]).unwrap();
    for evidence in [None, Some(&root), Some(&context)] {
        let original = report("Unused value");
        let mut groups = ReportGroups::default();
        if let Some(evidence) = evidence {
            groups.insert(original.clone(), evidence);
            groups.insert(original.clone(), evidence);
        } else {
            groups.insert_source(original.clone());
            groups.insert_source(original.clone());
        }
        let reports = groups.finish(&sources).unwrap();
        assert_eq!(reports.len(), 1);
        assert_eq!(reports[0].message(), original.message());
        assert_eq!(reports[0].primary(), original.primary());
        assert_eq!(reports[0].notes(), original.notes());
        let expected = evidence.map_or(0, |evidence| evidence.call_path().len());
        assert_eq!(reports[0].secondary().len(), expected);
        for label in reports[0].secondary() {
            assert_eq!(label.message, "Reached through this call.");
        }
    }
}

#[test]
fn distinct_messages_primary_labels_evidence_notes_and_severity_stay_separate() {
    let loaded = loaded("template Root(){}");
    let sources = SourceMap::from_loaded(&loaded, &[SourceId::new(0)]).unwrap();
    let mut originals = vec![report("first"), report("second")];
    let mut primary = Report::warning("first".into(), ReportCode::UnusedVariableValue);
    primary.add_primary(1..2, 0, "unused value".into());
    originals.push(primary);
    let mut primary_label = Report::warning("first".into(), ReportCode::UnusedVariableValue);
    primary_label.add_primary(0..1, 0, "another claim".into());
    originals.push(primary_label);
    let mut evidence = report("first");
    evidence.add_secondary(2..3, 0, Some("proof A".into()));
    originals.push(evidence);
    let mut evidence = report("first");
    evidence.add_secondary(2..3, 0, Some("proof B".into()));
    originals.push(evidence);
    let mut notes = report("first");
    notes.add_note("scope restriction".into());
    originals.push(notes);
    let mut error = Report::error("first".into(), ReportCode::UnusedVariableValue);
    error.add_primary(0..1, 0, "unused value".into());
    originals.push(error);
    let mut different_rule = Report::warning("first".into(), ReportCode::UnconstrainedSignal);
    different_rule.add_primary(0..1, 0, "unused value".into());
    originals.push(different_rule);
    let mut groups = ReportGroups::default();
    for report in &originals {
        groups.insert_source(report.clone());
        groups.insert_source(report.clone());
    }
    let reports = groups.finish(&sources).unwrap();
    assert_eq!(reports.len(), originals.len());
    for (actual, expected) in reports.iter().zip(&originals) {
        assert_eq!(actual.to_diagnostic(true), expected.to_diagnostic(true));
    }
}

const NESTED: &str = "function Issue(n){return n;}function Left(n){return Issue(n);}\
    function Right(n){return Issue(n);}template Root(){var a=Left(1);var b=Right(2);\
    var c=Left(3);var unaffected=Right(4);}";

#[test]
fn shared_and_crossing_paths_keep_context_steps_without_unaffected_calls() {
    let loaded = loaded(NESTED);
    let project = lift_project(&loaded);
    let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let sources = SourceMap::from_loaded(&loaded, &[SourceId::new(0)]).unwrap();
    let mut contexts = Vec::new();
    for parent in child_contexts(&provider, &root_context(&provider)) {
        contexts.extend(child_contexts(&provider, &parent));
    }
    assert_eq!(contexts.len(), 4);
    let mut groups = ReportGroups::default();
    for context in &contexts[..3] {
        groups.insert(report("Unused value"), context);
    }
    let reports = groups.finish(&sources).unwrap();
    let labels = reports[0].secondary();
    assert_eq!(labels.len(), 5);
    let left_call = contexts[0].call_path()[1].span().start();
    let label = labels.iter().find(|label| label.range.start == left_call).unwrap();
    assert_eq!(label.message, "Observed in analyzed context 1 (call 2), context 3 (call 2).",);
    let unaffected = contexts[3].call_path()[0].span().start();
    assert!(labels.iter().all(|label| label.range.start != unaffected));
    let mut reversed = ReportGroups::default();
    for context in contexts[..3].iter().rev() {
        reversed.insert(report("Unused value"), context);
    }
    let reversed = reversed.finish(&sources).unwrap();
    assert_eq!(reports[0].to_diagnostic(true), reversed[0].to_diagnostic(true));
}

#[test]
fn repeated_recursive_call_span_keeps_each_step_in_each_context() {
    let loaded = loaded(
        "template Rec(n){if(n){component child=Rec(n-1);}}\
        template Root(){component child=Rec(3);}",
    );
    let project = lift_project(&loaded);
    let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let sources = SourceMap::from_loaded(&loaded, &[SourceId::new(0)]).unwrap();
    let mut parent = root_context(&provider);
    let mut groups = ReportGroups::default();
    for _ in 0..3 {
        parent = child_contexts(&provider, &parent).remove(0);
        groups.insert(report("Unused value"), &parent);
    }
    assert_eq!(parent.call_path().len(), 3);
    assert_eq!(parent.call_path()[1], parent.call_path()[2]);
    let reports = groups.finish(&sources).unwrap();
    let labels = reports[0].secondary();
    assert_eq!(labels.len(), 2);
    let recursive = parent.call_path()[1].span().start();
    let label = labels.iter().find(|label| label.range.start == recursive).unwrap();
    assert_eq!(
        label.message,
        "Observed in analyzed context 1 (call 2), context 1 (call 3), context 2 (call 2)."
    );
}

#[test]
fn same_source_call_path_retains_distinct_argument_contexts() {
    let loaded = loaded("function Issue(n){return n;}template Root(){var value=Issue(-1);}");
    let project = lift_project(&loaded);
    let sources = SourceMap::from_loaded(&loaded, &[SourceId::new(0)]).unwrap();
    let mut contexts = Vec::new();
    for curve in [Curve::Bn254, Curve::Goldilocks] {
        let provider = ProjectAnalysis::build(&project, curve).unwrap();
        contexts.extend(child_contexts(&provider, &root_context(&provider)));
    }
    assert_ne!(contexts[0].context().arguments(), contexts[1].context().arguments());
    assert_eq!(contexts[0].call_path()[0].span(), contexts[1].call_path()[0].span());
    let mut groups = ReportGroups::default();
    for context in &contexts {
        groups.insert(report("Unused value"), context);
    }
    let reports = groups.finish(&sources).unwrap();
    assert_eq!(reports.len(), 1);
    assert_eq!(reports[0].secondary().len(), 1);
    assert_eq!(
        reports[0].secondary()[0].message,
        "Observed in analyzed context 1 (call 1), context 2 (call 1)."
    );
}

#[test]
fn unknown_or_invalid_call_path_sources_are_errors() {
    let loaded = loaded("function Issue(n){return n;}template Root(){var value=Issue(1);}");
    let project = lift_project(&loaded);
    let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let context = child_contexts(&provider, &root_context(&provider)).remove(0);
    let mut missing = loaded.clone();
    missing.files.clear();
    let mut shortened = loaded.clone();
    shortened.files[0].text.clear();
    for invalid in [&missing, &shortened] {
        let sources = SourceMap::from_loaded(invalid, &[]).unwrap();
        let mut groups = ReportGroups::default();
        groups.insert(report("Unused value"), &context);
        let error = groups.finish(&sources).err().unwrap();
        if invalid.files.is_empty() {
            assert_eq!(error, RenderError::UnknownSource(SourceId::new(0)));
        } else {
            assert_eq!(error, RenderError::InvalidSpan(context.call_path()[0].span()));
        }
    }
}

#[test]
fn no_reports_produce_no_findings() {
    let loaded = loaded("");
    let sources = SourceMap::from_loaded(&loaded, &[]).unwrap();
    assert!(ReportGroups::default().finish(&sources).unwrap().is_empty());
}
