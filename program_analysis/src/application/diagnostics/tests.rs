use std::collections::HashSet;
use std::fs;

use parser::frontend::{load_sources, Version, VersionPolicy};
use parser::hir::{lift_project, DefinitionRef};
use program_structure::constants::Curve;
use program_structure::report::MessageCategory;
use program_structure::writers::{OutputPolicy, ReportFilter};

use crate::application::coverage::{CoverageExplanation, CoverageKind};
use crate::application::diagnostics::Diagnostics;
use crate::hir_cfg::build_cfg;
use crate::interprocedural::{CallOwner, CallReachability, ProjectAnalysis};
use crate::rules::{RuleKind, SourceMap};

#[test]
fn a_warning_never_promotes_missing_context_from_the_same_scope() {
    let path = std::env::temp_dir().join(format!(
        "circomspect-coverage-severity-{}-{:?}.circom",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::write(&path, "pragma circom 2.2.3;template Example(n){}").unwrap();
    let loaded =
        load_sources(std::slice::from_ref(&path), &[], VersionPolicy::new(Version::new(2, 2, 3)));
    fs::remove_file(path).unwrap();
    let lifted = lift_project(&loaded);
    let definition = lifted.hir.definition("Example").unwrap();
    let DefinitionRef::Template(id) = definition else { panic!("template") };
    let span = lifted.hir.template(id).unwrap().name_span;
    let project = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = project.contexts().symbolic_root(definition).unwrap();
    let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
    let mut diagnostics = Diagnostics::new(&sources);
    let explanations = vec![
        CoverageExplanation {
            kind: CoverageKind::MissingContext,
            span,
            message: "parameter `n` is unknown".into(),
            help: "Analyze a caller supplying `n`.".into(),
        },
        CoverageExplanation {
            kind: CoverageKind::ResourceLimit,
            span,
            message: "The analysis work limit was reached.".into(),
            help: "Review the affected check manually.".into(),
        },
    ];
    diagnostics.scope_incomplete(&evidence, span, explanations, Some(RuleKind::FieldArithmetic));
    let reports = diagnostics.finish().unwrap();
    assert_eq!(reports.len(), 2);
    let policy = OutputPolicy::new(MessageCategory::Warning, HashSet::from([0]), HashSet::new());
    let visible: Vec<_> = reports.iter().filter(|report| policy.filter(report)).collect();
    assert_eq!(visible.len(), 1);
    assert_eq!(visible[0].category(), &MessageCategory::Warning);
    assert!(visible[0].secondary().iter().all(|label| !label.message.contains("parameter")));
    assert!(visible[0].notes().iter().all(|note| !note.contains("caller")));
    let info = reports.iter().find(|report| report.category() == &MessageCategory::Info).unwrap();
    assert!(info.secondary().iter().any(|label| label.message.contains("parameter `n`")));
}

#[test]
fn a_source_notice_retains_both_contributing_call_paths() {
    let path = std::env::temp_dir().join(format!(
        "circomspect-source-coverage-{}-{:?}.circom",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::write(
        &path,
        "pragma circom 2.2.3;template Child(n){signal output out;out<==n;}\
        template Parent(){component a=Child(1);component b=Child(2);}",
    )
    .unwrap();
    let loaded =
        load_sources(std::slice::from_ref(&path), &[], VersionPolicy::new(Version::new(2, 2, 3)));
    fs::remove_file(path).unwrap();
    let lifted = lift_project(&loaded);
    let definition = lifted.hir.definition("Parent").unwrap();
    let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
        panic!("template")
    };
    let span = lifted.hir.template(child).unwrap().name_span;
    let project = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let parent = project.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = project.contexts().analyze_for_evidence(&cfg, &parent, None).unwrap();
    let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
    let mut diagnostics = Diagnostics::new(&sources);
    let explanation = CoverageExplanation {
        kind: CoverageKind::Unsupported,
        span,
        message: "This check does not resolve parallel expression values.".into(),
        help: "Review the parallel expression and its uses manually.".into(),
    };
    diagnostics.source_incomplete(explanation.clone());
    let mut calls = 0;
    for site in project.graph().calls_from(CallOwner::Definition(definition)) {
        let CallReachability::Reachable(call) = project.graph().reachable_call(site.id(), &facts)
        else {
            panic!("reachable child")
        };
        let evidence = project.contexts().call_evidence(&call, &facts, &parent).unwrap();
        diagnostics.scope_incomplete(
            &evidence,
            span,
            vec![explanation.clone()],
            Some(RuleKind::FieldArithmetic),
        );
        calls += 1;
    }
    assert_eq!(calls, 2);
    let reports = diagnostics.finish().unwrap();
    assert_eq!(reports.len(), 1);
    let paths: Vec<_> =
        reports[0].secondary().iter().filter(|label| label.message.contains("context")).collect();
    assert_eq!(paths.len(), 2);
    assert!(paths.iter().any(|label| label.message.contains("context 1")));
    assert!(paths.iter().any(|label| label.message.contains("context 2")));
}
