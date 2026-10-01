use circomspect_program_analysis::hir_facts::{FieldContext, Range};
use circomspect_program_analysis::interprocedural::{ArgumentValue, ProjectSummaries, SummaryBlocker};
use parser::hir::{lower_project, DefinitionRef, LoweredProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;
use std::fs;

fn fixture(source: &str) -> LoweredProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-phase5-summary-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lower_project(&loaded)
}

#[test]
fn concrete_scalar_function_summary_specializes_return_and_branch() {
    let lowered = fixture("function F(n){if(n){return n+2;}return 2;}");
    let provider = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let DefinitionRef::Function(function) = lowered.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let field = FieldContext::for_curve(Curve::Bn254);
    let zero = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Scalar(field.canonical(0.into()))],
        )
        .unwrap();
    let one = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Scalar(field.canonical(1.into()))],
        )
        .unwrap();
    let zero_summary = provider.function(function, &zero);
    let one_summary = provider.function(function, &one);
    assert_eq!(
        zero_summary.certified().unwrap().returns(),
        &Range::Exact(field.canonical(2.into()))
    );
    assert_eq!(
        one_summary.certified().unwrap().returns(),
        &Range::Exact(field.canonical(3.into()))
    );
    assert!(provider
        .function(
            function,
            &provider.symbolic_context_for(DefinitionRef::Function(function)).unwrap()
        )
        .unavailable()
        .is_some());
}

#[test]
fn foreign_and_non_scalar_contexts_never_certify_function_returns() {
    let lowered = fixture("function F(n){return n;}");
    let provider = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let DefinitionRef::Function(function) = lowered.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let array = provider
        .context_for(DefinitionRef::Function(function), vec![ArgumentValue::Array(vec![])])
        .unwrap();
    assert!(provider.function(function, &array).unavailable().is_some());
    let other = fixture("function F(n){return 1;}");
    let DefinitionRef::Function(foreign) = other.hir.definition("F").unwrap() else {
        panic!("foreign function F")
    };
    assert_eq!(
        provider.function(foreign, &array).unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::ForeignDefinition]))
    );
}

#[test]
fn symbolic_library_root_certifies_a_parameter_independent_return() {
    let lowered = fixture("function F(n){return 7;}");
    let provider = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let DefinitionRef::Function(function) = lowered.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let context = provider.symbolic_context_for(DefinitionRef::Function(function)).unwrap();
    let summary = provider.function(function, &context);
    let field = FieldContext::for_curve(Curve::Bn254);
    assert_eq!(summary.certified().unwrap().returns(), &Range::Exact(field.canonical(7.into())));
    assert!(summary.certified().unwrap().input_dependencies().is_empty());
}

#[test]
fn scalar_context_cannot_validate_an_indexed_parameter_use() {
    let lowered = fixture("function F(n){return n[0];}");
    let provider = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let DefinitionRef::Function(function) = lowered.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let field = FieldContext::for_curve(Curve::Bn254);
    let context = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Scalar(field.canonical(1.into()))],
        )
        .unwrap();
    assert!(provider.function(function, &context).unavailable().is_some());
}
