// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
mod support;

use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::interprocedural::{
    AnalyzeEvidenceError, CallOwner, CallReachability, ProjectSummaries,
};
use circomspect_program_analysis::new_rules::SourceMap;
use parser::hir::{lift_project, SemanticCode, SemanticDiagnostic, Severity};
use parser::frontend::{load_sources, LoadedProject, SourceId, Span, Version, VersionPolicy};
use program_structure::report::MessageCategory;
use program_structure::utils::constants::Curve;
use serde_json::Value;

fn fixture(source: &str) -> LoadedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-semantic-render-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("main.circom");
    fs::write(&path, source).unwrap();
    load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)))
}

#[test]
fn reachable_array_argument_renders_t2000_with_exact_source_location() {
    let source = concat!(
        "template Child(n){var x=n;x=1;signal output out;out<==1;} ",
        "template Parent(){component c=Child([1,2]);} component main=Parent();"
    );
    let loaded = fixture(source);
    let lifted = lift_project(&loaded);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let child = lifted.hir.definition("Child").unwrap();
    let parent_cfg = build_cfg(&lifted.hir, parent).unwrap();
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main_call) =
        provider.graph().reachable_main_call(main.id(), provider.hir())
    else {
        panic!("main call must be reachable");
    };
    let caller = provider.main_evidence(&main_call).unwrap();
    let parent_facts = provider.analyze_for_evidence(&parent_cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_call(site.id(), &parent_facts)
    else {
        panic!("child call must be reachable");
    };
    let evidence = provider.call_evidence(&call, &parent_facts, &caller).unwrap();
    let child_cfg = build_cfg(&lifted.hir, child).unwrap();
    let error = provider.analyze_for_evidence(&child_cfg, &evidence, None).err().unwrap();
    let AnalyzeEvidenceError::InvalidAssignment { diagnostic, .. } = error else {
        panic!("aggregate argument must invalidate the scalar write");
    };
    assert_eq!(diagnostic.code, SemanticCode::InvalidAssignment);
    assert_eq!(diagnostic.severity, Severity::Error);
    assert_eq!(&source[diagnostic.span.start()..diagnostic.span.end()], "n");

    let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
    let report = sources.semantic_report(&diagnostic).unwrap();
    assert_eq!(report.id(), "T2000");
    assert_eq!(*report.category(), MessageCategory::Error);
    assert_eq!(report.message(), &diagnostic.message);
    assert_eq!(report.primary()[0].range, diagnostic.span.start()..diagnostic.span.end());
    let terminal = report.to_diagnostic(true);
    assert_eq!(terminal.code.as_deref(), Some("T2000"));
    assert_eq!(terminal.message, diagnostic.message);
    assert_eq!(terminal.labels[0].range, diagnostic.span.start()..diagnostic.span.end());

    let output = loaded.files[0].path.with_extension("sarif.json");
    assert_eq!(
        support::render_reports(
            std::slice::from_ref(&report),
            &sources,
            MessageCategory::Error,
            &[],
            &output,
        ),
        (1, 1)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
    let result = &sarif["runs"][0]["results"][0];
    assert_eq!(result["ruleId"], "T2000");
    assert_eq!(result["level"], "error");
    assert_eq!(result["message"]["text"], diagnostic.message);
    let region = &result["locations"][0]["physicalLocation"]["region"];
    assert_eq!(region["startLine"], 1);
    assert_eq!(region["startColumn"], diagnostic.span.start() + 1);
    assert_eq!(region["endColumn"], diagnostic.span.end() + 1);

    assert_eq!(
        support::render_reports(&[report], &sources, MessageCategory::Error, &["T2000"], &output),
        (0, 0)
    );
}

#[test]
fn static_hir_warnings_use_the_same_converter_and_existing_filters() {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-semantic-include-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let root = directory.join("main.circom");
    fs::write(&root, "include \"lib.circom\"; template Root() {} component main=Root();").unwrap();
    fs::write(directory.join("lib.circom"), "function F(x,x){var y=1; {var y=2;} return x+y;}")
        .unwrap();
    let loaded = load_sources(
        &[root],
        std::slice::from_ref(&directory),
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    let lifted = lift_project(&loaded);
    let root = &loaded.files[0];
    let included = &loaded.files[1];
    let diagnostics: Vec<_> =
        lifted.diagnostics.iter().filter(|item| item.span.source() == included.id).collect();
    assert_eq!(diagnostics.len(), 2);
    assert_eq!(diagnostics[0].code, SemanticCode::ParameterCollision);
    assert_eq!(diagnostics[1].code, SemanticCode::Shadowing);

    let all_roots = SourceMap::from_loaded(&loaded, &[root.id, included.id]).unwrap();
    let reports: Vec<_> = diagnostics
        .iter()
        .map(|diagnostic| all_roots.semantic_report(diagnostic).unwrap())
        .collect();
    assert_eq!(
        reports.iter().map(program_structure::report::Report::id).collect::<Vec<_>>(),
        ["CS0002", "CS0001"]
    );
    assert!(reports.iter().all(|report| *report.category() == MessageCategory::Warning));
    let output = root.path.with_extension("sarif.json");
    assert_eq!(
        support::render_reports(&reports, &all_roots, MessageCategory::Warning, &[], &output),
        (2, 2)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
    assert_eq!(sarif["runs"][0]["results"].as_array().unwrap().len(), 2);

    assert_eq!(
        support::render_reports(&reports, &all_roots, MessageCategory::Error, &[], &output),
        (0, 0)
    );
    assert_eq!(
        support::render_reports(&reports, &all_roots, MessageCategory::Info, &["CS0002"], &output),
        (1, 1)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
    assert_eq!(sarif["runs"][0]["results"][0]["ruleId"], "CS0001");

    let root_only = SourceMap::from_loaded(&loaded, &[root.id]).unwrap();
    assert_eq!(
        support::render_reports(&reports, &root_only, MessageCategory::Info, &[], &output),
        (0, 0)
    );
    assert_eq!(
        support::render(&[], &root_only, MessageCategory::Info, &[], &output).unwrap(),
        (0, 0)
    );
}

#[test]
fn every_semantic_code_retains_its_declared_id() {
    let loaded = fixture("template T() {}\n");
    let source = &loaded.files[0];
    let sources = SourceMap::from_loaded(&loaded, &[source.id]).unwrap();
    let span = Span::checked(source.id, 0..1, &source.text).unwrap();
    let codes = [
        SemanticCode::MissingCall,
        SemanticCode::WrongFunction,
        SemanticCode::WrongTemplate,
        SemanticCode::DuplicateFunction,
        SemanticCode::DuplicateTemplate,
        SemanticCode::DuplicateSymbol,
        SemanticCode::Shadowing,
        SemanticCode::ParameterCollision,
        SemanticCode::MissingBusType,
        SemanticCode::InvalidAssignment,
        SemanticCode::WrongBusAssignment,
        SemanticCode::WrongAssignmentExpression,
        SemanticCode::WrongAssignmentRank,
        SemanticCode::InvalidCallArgument,
        SemanticCode::InvalidSignalAccess,
        SemanticCode::InvalidTag,
        SemanticCode::InputTagAccess,
        SemanticCode::InvalidTagAfterArray,
        SemanticCode::InvalidArrayAccess,
        SemanticCode::InvalidArrayIndexDimension,
        SemanticCode::InvalidArrayIndexBus,
        SemanticCode::AnonymousInput,
        SemanticCode::ForbiddenDeclaration,
        SemanticCode::TemplateReturn,
        SemanticCode::ConstraintInFunction,
        SemanticCode::UnknownSymbol,
        SemanticCode::WrongArity,
        SemanticCode::NonConstantArrayLength,
        SemanticCode::NonComputableExpression,
        SemanticCode::FeatureVersion,
    ];
    for code in codes {
        let diagnostic = SemanticDiagnostic {
            code,
            severity: Severity::Error,
            span,
            message: "semantic error".to_string(),
            expected_kind: None,
            actual_kind: None,
        };
        let report = sources.semantic_report(&diagnostic).unwrap();
        assert_eq!(report.id(), code.as_str(), "{code:?}");
    }
    let wrong_arity = SemanticDiagnostic {
        code: SemanticCode::WrongArity,
        severity: Severity::Error,
        span,
        message: "wrong number of arguments".to_string(),
        expected_kind: None,
        actual_kind: None,
    };
    assert_eq!(sources.semantic_report(&wrong_arity).unwrap().name(), "wrong-number-of-arguments");
}

#[test]
fn semantic_converter_rejects_unknown_and_invalid_source_spans() {
    let loaded = fixture("function F(x,x){return x;} // π\n");
    let lifted = lift_project(&loaded);
    let source = &loaded.files[0];
    let sources = SourceMap::from_loaded(&loaded, &[source.id]).unwrap();
    let diagnostic = lifted.diagnostics.first().unwrap();
    assert_eq!(diagnostic.code, SemanticCode::ParameterCollision);
    let unknown = Span::checked(SourceId::new(42), 0..0, "").unwrap();
    let oversized = Span::checked(source.id, 0..100, &"x".repeat(100)).unwrap();
    let pi = source.text.find('π').unwrap();
    let split_utf8 = Span::checked(source.id, pi..pi + 1, &"x".repeat(100)).unwrap();
    for (span, expected) in [
        (
            unknown,
            circomspect_program_analysis::new_rules::RenderError::UnknownSource(unknown.source()),
        ),
        (oversized, circomspect_program_analysis::new_rules::RenderError::InvalidSpan(oversized)),
        (split_utf8, circomspect_program_analysis::new_rules::RenderError::InvalidSpan(split_utf8)),
    ] {
        let mut invalid = diagnostic.clone();
        invalid.span = span;
        assert_eq!(sources.semantic_report(&invalid).err(), Some(expected));
    }
}

#[test]
fn concrete_parameter_index_error_uses_terminal_and_sarif_source_ranges() {
    let source = "template T(n){n[1]=1;} component main=T([2]);";
    let loaded = fixture(source);
    let lifted = lift_project(&loaded);
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), provider.hir())
    else {
        panic!("main must be reachable")
    };
    let evidence = provider.main_evidence(&call).unwrap();
    let cfg = build_cfg(provider.hir(), evidence.context().definition()).unwrap();
    let error = provider.analyze_for_evidence(&cfg, &evidence, None).err().unwrap();
    let diagnostic = error.diagnostic().unwrap();
    assert_eq!(diagnostic.code, SemanticCode::InvalidArrayAccess);
    assert_eq!(&source[diagnostic.span.start()..diagnostic.span.end()], "n[1]");
    let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
    let report = sources.semantic_report(diagnostic).unwrap();
    let terminal = report.to_diagnostic(true);
    assert_eq!(terminal.code.as_deref(), Some("T2032"));
    assert_eq!(terminal.labels[0].range, diagnostic.span.start()..diagnostic.span.end());
    let output = loaded.files[0].path.with_extension("parameter.sarif.json");
    assert_eq!(
        support::render_reports(
            std::slice::from_ref(&report),
            &sources,
            MessageCategory::Error,
            &[],
            &output,
        ),
        (1, 1)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
    let result = &sarif["runs"][0]["results"][0];
    assert_eq!(result["ruleId"], "T2032");
    assert_eq!(result["level"], "error");
    let region = &result["locations"][0]["physicalLocation"]["region"];
    assert_eq!(region["startColumn"], diagnostic.span.start() + 1);
    assert_eq!(region["endColumn"], diagnostic.span.end() + 1);
    assert_eq!(
        support::render_reports(&[report], &sources, MessageCategory::Error, &["T2032"], &output),
        (0, 0)
    );
}
