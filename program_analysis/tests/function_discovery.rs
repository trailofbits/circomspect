// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]

use std::collections::BTreeSet;
use std::fs;

use circomspect_program_analysis::hir_facts::{FieldContext, Range};
use circomspect_program_analysis::interprocedural::{
    ArgumentValue, CallContext, CallOwner, CallProvenance, FunctionEffect, FunctionEffects,
    FunctionSummary, ProjectAnalysis, SummaryBlocker, SummaryFact,
};
use parser::hir::{lift_project, DefinitionRef, FunctionId, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

const CHAIN: &str = "function F(n){if(n){return F(n-1);}log(1);return 7;}";
const DUPLICATES: &str = "function F(n){if(n){log(F(0));return F(n-1);}return 7;}";

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-function-discovery-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let project = load_sources(
        std::slice::from_ref(&path),
        std::slice::from_ref(&directory),
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    let lifted = lift_project(&project);
    fs::remove_file(path).unwrap();
    fs::remove_dir(directory).unwrap();
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    lifted
}

fn function(project: &LiftedProject, name: &str) -> FunctionId {
    let DefinitionRef::Function(function) = project.hir.definition(name).unwrap() else {
        panic!("expected function {name}")
    };
    function
}

fn contexts(provider: &ProjectAnalysis<'_>, function: FunctionId, count: u32) -> Vec<CallContext> {
    let field = FieldContext::for_curve(Curve::Bn254);
    let mut contexts = Vec::new();
    for argument in 0..count {
        let value = ArgumentValue::Scalar(field.canonical(argument.into()));
        let context =
            provider.context_for(DefinitionRef::Function(function), vec![value.clone()]).unwrap();
        assert_eq!(context.arguments(), [value]);
        assert_eq!(context.definition(), DefinitionRef::Function(function));
        contexts.push(context);
    }
    assert_eq!(contexts.iter().collect::<BTreeSet<_>>().len(), count as usize);
    for pair in contexts.windows(2) {
        assert!(pair[0] < pair[1]);
    }
    contexts
}

fn assert_exact_return(summary: &SummaryFact<FunctionSummary>) {
    let field = FieldContext::for_curve(Curve::Bn254);
    let summary = summary.certified().expect("complete exact return");
    assert_eq!(summary.complete_return(), Some(&Range::Exact(field.canonical(7.into()))));
    assert_eq!(summary.input_dependencies(), &BTreeSet::new());
}

fn assert_log_effect(effects: &SummaryFact<FunctionEffects>) {
    let effects = effects.certified().expect("complete effects");
    assert!(!effects.is_empty());
    assert!(effects.contains(FunctionEffect::Log));
    assert!(!effects.contains(FunctionEffect::Assert));
}

fn assert_recursive_sites(provider: &ProjectAnalysis<'_>, function: FunctionId, count: usize) {
    let sites =
        provider.graph().calls_from(CallOwner::Definition(DefinitionRef::Function(function)));
    assert_eq!(sites.len(), count);
    for site in sites {
        assert_eq!(site.resolved(), Some(DefinitionRef::Function(function)));
        assert_eq!(site.provenance, CallProvenance::DeferredControl);
    }
}

#[test]
fn return_discovery_preserves_exact_context_budget_boundary() {
    let lifted = fixture(CHAIN);
    let function = function(&lifted, "F");
    for count in [63, 64, 65] {
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        assert_recursive_sites(&provider, function, 1);
        let contexts = contexts(&provider, function, count);
        let context = contexts.last().unwrap();
        let first = provider.function(function, context);
        let repeated = provider.function(function, context);
        assert_eq!(first, repeated);
        if count == 65 {
            assert_eq!(first.unavailable(), Some(&BTreeSet::from([SummaryBlocker::ContextBudget])));
        } else {
            assert_exact_return(&first);
        }
    }
}

#[test]
fn effect_discovery_preserves_exact_context_budget_boundary() {
    let lifted = fixture(CHAIN);
    let function = function(&lifted, "F");
    for count in [63, 64, 65] {
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        assert_recursive_sites(&provider, function, 1);
        let contexts = contexts(&provider, function, count);
        let context = contexts.last().unwrap();
        let first = provider.function_effects(function, context);
        let repeated = provider.function_effects(function, context);
        assert_eq!(first, repeated);
        if count == 65 {
            assert_eq!(first.unavailable(), Some(&BTreeSet::from([SummaryBlocker::ContextBudget])));
        } else {
            assert_log_effect(&first);
        }
    }
}

#[test]
fn return_discovery_ignores_pending_duplicates_at_capacity() {
    let lifted = fixture(DUPLICATES);
    let function = function(&lifted, "F");
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    assert_recursive_sites(&provider, function, 2);
    let contexts = contexts(&provider, function, 64);
    assert!(contexts[0] < contexts[62]);
    let first = provider.function(function, &contexts[63]);
    assert_exact_return(&first);
    assert_eq!(first, provider.function(function, &contexts[63]));
}

#[test]
fn effect_discovery_ignores_pending_duplicates_at_capacity() {
    let lifted = fixture(DUPLICATES);
    let function = function(&lifted, "F");
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    assert_recursive_sites(&provider, function, 2);
    let contexts = contexts(&provider, function, 64);
    assert!(contexts[0] < contexts[62]);
    let first = provider.function_effects(function, &contexts[63]);
    assert_log_effect(&first);
    assert_eq!(first, provider.function_effects(function, &contexts[63]));
}

#[test]
fn return_and_effect_queries_keep_their_distinct_entry_error_order() {
    let lifted = fixture("function F(n){return n;}");
    let foreign = fixture("function F(n){return n;}");
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let context = provider.symbolic_context_for(lifted.hir.definition("F").unwrap()).unwrap();
    let function = function(&foreign, "F");
    assert_eq!(
        provider.function(function, &context).unavailable(),
        Some(&BTreeSet::from([SummaryBlocker::ForeignDefinition]))
    );
    assert_eq!(
        provider.function_effects(function, &context).unavailable(),
        Some(&BTreeSet::from([SummaryBlocker::WrongContext]))
    );
}

#[test]
fn recursive_returns_refuse_while_effects_solve_the_repeated_context() {
    let lifted = fixture("function F(n){log(1);return F(n);}");
    let function = function(&lifted, "F");
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let contexts = contexts(&provider, function, 1);
    assert_eq!(
        provider.function(function, &contexts[0]).unavailable(),
        Some(&BTreeSet::from([SummaryBlocker::RecursiveCycle]))
    );
    assert_log_effect(&provider.function_effects(function, &contexts[0]));
}
