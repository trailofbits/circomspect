use std::collections::BTreeSet;
use std::fs;

use parser::hir::{lift_project, DefinitionRef, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::constants::Curve;

use crate::hir_cfg::build_cfg;
use crate::interprocedural::{
    CallOwner, CallReachability, ContextEvidence, ProjectAnalysis, SummaryBlocker,
};
use crate::rules::{RuleContext, RuleContextError};

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-rule-cache-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty());
    lifted
}

fn with_context(source: &str, budget: Option<usize>, check: impl FnOnce(&RuleContext<'_, '_, '_>)) {
    let lifted = fixture(source);
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, budget).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    check(&context);
}

fn assert_direct_results(context: &RuleContext<'_, '_, '_>) {
    assert!(context.warning_execution.get().is_none());
    assert!(context.component_outputs.get().is_none());
    let expected_execution = context
        .summaries
        .execution()
        .check_warning_execution_scope(context.facts, context.evidence);
    let expected_outputs =
        context.summaries.components().exact_component_outputs(context.facts, context.evidence);
    for _ in 0..3 {
        assert_eq!(context.check_warning_execution_scope(), expected_execution);
        assert_eq!(context.exact_component_outputs(), expected_outputs);
        assert_eq!(context.warning_execution.get(), Some(&expected_execution));
        assert_eq!(context.component_outputs.get(), Some(&expected_outputs));
        assert_eq!(
            context
                .summaries
                .execution()
                .check_warning_execution_scope(context.facts, context.evidence),
            expected_execution
        );
        assert_eq!(
            context.summaries.components().exact_component_outputs(context.facts, context.evidence),
            expected_outputs
        );
    }
}

#[test]
fn caches_preserve_complete_results_and_all_blockers() {
    for source in [
        "template T(){}",
        "template T(){assert(0);}",
        "function Fail(){assert(0);return 7;}template T(){var unused=Fail();}",
        "template Child(){signal output out;out<==1;}template T(){component c=Child();}",
        "template T(){component c=Missing();}",
        "template Child(n){signal output out[n];}template T(n){component c=Child(n);}",
    ] {
        with_context(source, None, assert_direct_results);
    }
    with_context("template T(){signal output out;out<==1;}", Some(0), assert_direct_results);
}

#[test]
fn output_and_execution_budget_refusals_remain_unavailable() {
    with_context(
        "template Child(){signal output out[257];}template T(){component c=Child();}",
        None,
        |context| {
            assert_direct_results(context);
            assert_eq!(
                context.exact_component_outputs().unavailable(),
                Some(&BTreeSet::from([SummaryBlocker::ContextBudget]))
            );
        },
    );
    with_context(
        "function F(n){if(n){return F(n-1);}assert(0);return 7;}
         template T(){var unused=F(64);signal output out;out<==1;}",
        None,
        |context| {
            assert_direct_results(context);
            assert_eq!(context.check_warning_execution_scope(), Err(SummaryBlocker::ContextBudget));
        },
    );
}

fn child_evidence(provider: &ProjectAnalysis<'_>, parent: &str) -> ContextEvidence {
    let definition = provider.hir().definition(parent).unwrap();
    let root = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(provider.hir(), definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &root, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("expected reachable child")
    };
    provider.contexts().call_evidence(&call, &facts, &root).unwrap()
}

#[test]
fn parameter_specializations_and_call_ancestries_keep_separate_caches() {
    let lifted = fixture(concat!(
        "function Warm(){return 1;}",
        "template Child(n){signal output out[n];}",
        "template T(n){component c=Child(n);}",
        "template One(){component t=T(1);}",
        "template Two(){component t=T(2);}",
        "template AnotherOne(){component t=T(1);}",
    ));
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let first = child_evidence(&provider, "One");
    let second = child_evidence(&provider, "Two");
    let another = child_evidence(&provider, "AnotherOne");
    assert_eq!(first.context(), another.context());
    assert_ne!(first, another);
    let cfg = build_cfg(&lifted.hir, first.context().definition()).unwrap();
    let first_facts = provider.contexts().analyze_for_evidence(&cfg, &first, None).unwrap();
    let second_facts = provider.contexts().analyze_for_evidence(&cfg, &second, None).unwrap();
    let another_facts = provider.contexts().analyze_for_evidence(&cfg, &another, None).unwrap();
    let contexts = [
        RuleContext::new(&first_facts, &provider, &first).unwrap(),
        RuleContext::new(&second_facts, &provider, &second).unwrap(),
        RuleContext::new(&another_facts, &provider, &another).unwrap(),
    ];
    for context in &contexts {
        assert_direct_results(context);
    }
    let DefinitionRef::Function(warm) = lifted.hir.definition("Warm").unwrap() else {
        panic!("expected function")
    };
    let warm_context =
        provider.contexts().symbolic_context_for(DefinitionRef::Function(warm)).unwrap();
    assert!(provider.functions().function(warm, &warm_context).certified().is_some());
    for (context, length) in contexts.iter().zip([1, 2, 1]) {
        let outputs = context.exact_component_outputs();
        let outputs = outputs.certified().unwrap();
        assert_eq!(outputs.len(), length);
        for output in outputs {
            assert_eq!(output.applied_port().caller_evidence(), context.evidence);
        }
        assert_eq!(
            context.exact_component_outputs(),
            provider.components().exact_component_outputs(context.facts, context.evidence)
        );
    }
    assert_ne!(contexts[0].exact_component_outputs(), contexts[2].exact_component_outputs());
    assert_eq!(
        RuleContext::new(&first_facts, &provider, &another).err(),
        Some(RuleContextError::MismatchedFacts(SummaryBlocker::WrongContext))
    );
}

#[test]
fn populated_caches_do_not_relax_project_or_field_checks() {
    let lifted = fixture("template T(){signal output out;out<==1;}");
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let root = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &root, None).unwrap();
    assert_direct_results(&RuleContext::new(&facts, &provider, &root).unwrap());
    let other_field = ProjectAnalysis::build(&lifted, Curve::Goldilocks).unwrap();
    assert_eq!(
        RuleContext::new(&facts, &other_field, &root).err(),
        Some(RuleContextError::WrongCurve)
    );
    let foreign = fixture("template T(){signal output out;out<==1;}");
    let foreign = ProjectAnalysis::build(&foreign, Curve::Bn254).unwrap();
    assert_eq!(
        RuleContext::new(&facts, &foreign, &root).err(),
        Some(RuleContextError::ForeignProject)
    );
}
