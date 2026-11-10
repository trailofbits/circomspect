// Fixture assembly and assertions intentionally fail the test on errors.
#![allow(clippy::allow_attributes, clippy::panic, clippy::unwrap_used)]

#[path = "support/projects.rs"]
mod projects;

use std::collections::BTreeSet;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ContextEvidence, ProjectAnalysis, SummaryBlocker,
};
use circomspect_program_analysis::rules::{registered_rules, AbstentionReason, RuleContext, RuleKind};
use program_structure::constants::Curve;

const LARGE_LIBRARY: &str = "template Wide(n){signal output out[n];}\
    template Library(){component first=Wide(254);component second=Wide(254);}";

fn main_evidence(provider: &ProjectAnalysis<'_>) -> ContextEvidence {
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), provider.hir())
    else {
        panic!("fixture main must be reachable")
    };
    provider.contexts().main_evidence(&call).unwrap()
}

fn child_evidence(provider: &ProjectAnalysis<'_>, parent: &ContextEvidence) -> ContextEvidence {
    let definition = parent.context().definition();
    let cfg = build_cfg(provider.hir(), definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, parent, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("fixture child must be reachable")
    };
    provider.contexts().call_evidence(&call, &facts, parent).unwrap()
}

fn assert_refusal(context: &RuleContext<'_, '_, '_>, kind: RuleKind, blocker: SummaryBlocker) {
    let rule = registered_rules().find(|rule| rule.kind() == kind).unwrap();
    let result = rule.run(context);
    assert!(result.findings().is_empty());
    assert_eq!(result.abstentions().len(), 1);
    let abstention = &result.abstentions()[0];
    assert_eq!(abstention.kind, kind);
    assert_eq!(&abstention.context, context.call_context());
    assert_eq!(abstention.span, context.validated_header().unwrap().name_span());
    assert_eq!(abstention.reason, AbstentionReason::Summary(BTreeSet::from([blocker])));
}

#[test]
fn symbolic_large_library_rules_refuse_scope_before_output_budget() {
    let project = projects::lift_source(LARGE_LIBRARY, "circomspect-rule-scope-symbolic");
    let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let definition = provider.hir().definition("Library").unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(provider.hir(), definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let enumeration = provider.components().exact_component_outputs(&facts, &evidence);
    assert_eq!(enumeration.unavailable(), Some(&BTreeSet::from([SummaryBlocker::ContextBudget])));
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    for kind in [RuleKind::UnconstrainedLessThan, RuleKind::UnusedOutputSignal] {
        assert_refusal(&context, kind, SummaryBlocker::UnsupportedContext);
    }
}

#[test]
fn called_large_template_comparator_refuses_scope_before_output_budget() {
    let source = format!(
        "{LARGE_LIBRARY}template Main(){{component child=Library();}}component main=Main();"
    );
    let project = projects::lift_source(&source, "circomspect-rule-scope-call");
    let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let evidence = child_evidence(&provider, &main_evidence(&provider));
    let cfg = build_cfg(provider.hir(), evidence.context().definition()).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let enumeration = provider.components().exact_component_outputs(&facts, &evidence);
    assert_eq!(enumeration.unavailable(), Some(&BTreeSet::from([SummaryBlocker::ContextBudget])));
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    assert_refusal(&context, RuleKind::UnconstrainedLessThan, SummaryBlocker::UnsupportedContext);
    let unused =
        registered_rules().find(|rule| rule.kind() == RuleKind::UnusedOutputSignal).unwrap();
    let result = unused.run(&context);
    assert!(result.findings().is_empty());
    assert_eq!(result.abstentions(), []);
}

#[test]
fn symbolic_small_and_empty_libraries_retain_scope_abstention() {
    for (body, outputs) in [("", 0), ("component c=Wide(0);", 0), ("component c=Wide(1);", 1)] {
        let source =
            format!("template Wide(n){{signal output out[n];}}template Library(){{{body}}}");
        let project = projects::lift_source(&source, "circomspect-rule-scope-small");
        let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
        let definition = provider.hir().definition("Library").unwrap();
        let evidence = provider.contexts().symbolic_root(definition).unwrap();
        let cfg = build_cfg(provider.hir(), definition).unwrap();
        let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let enumeration = provider.components().exact_component_outputs(&facts, &evidence);
        assert_eq!(enumeration.certified().map(Vec::len), Some(outputs));
        let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
        assert_refusal(&context, RuleKind::UnusedOutputSignal, SummaryBlocker::UnsupportedContext);
    }
}

#[test]
fn actual_main_large_outputs_keep_the_enumeration_budget_refusal() {
    let source = format!("{LARGE_LIBRARY}component main=Library();");
    let project = projects::lift_source(&source, "circomspect-rule-scope-main");
    let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let evidence = main_evidence(&provider);
    let cfg = build_cfg(provider.hir(), evidence.context().definition()).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    for kind in [RuleKind::UnconstrainedLessThan, RuleKind::UnusedOutputSignal] {
        assert_refusal(&context, kind, SummaryBlocker::ContextBudget);
    }
}
