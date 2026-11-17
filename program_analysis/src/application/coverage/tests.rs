use std::collections::BTreeSet;
use std::fs;

use abstract_interpretation::graph::FlowGraph;
use parser::hir::{lift_project, ExprId, ExprKind, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::constants::Curve;

use crate::application::coverage::{CoverageContext, CoverageKind};
use crate::hir_cfg::{build_cfg, CfgNodeKind};
use crate::hir_facts::FactBlocker;
use crate::interprocedural::{CallOwner, CallReachability, ProjectAnalysis, SummaryBlocker};
use crate::rules::{run_registered, AbstentionReason, RuleContext};

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-coverage-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

fn with_context(source: &str, check: impl FnOnce(&CoverageContext<'_, '_>)) {
    let lifted = fixture(source);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = if lifted.hir.mains().is_empty() {
        provider.contexts().symbolic_root(definition).unwrap()
    } else {
        let site = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph().reachable_main_call(site.id(), provider.hir())
        else {
            panic!("reachable main")
        };
        provider.contexts().main_evidence(&call).unwrap()
    };
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let span = lifted.hir.templates()[0].name_span;
    check(&CoverageContext {
        hir: &lifted.hir,
        facts: Some(&facts),
        evidence: Some(&evidence),
        span,
    });
}

fn access(context: &CoverageContext<'_, '_>, name: &str) -> ExprId {
    context
        .hir
        .expressions()
        .iter()
        .find_map(|expression| {
            let ExprKind::Access(path) = &expression.kind else { return None };
            context
                .hir
                .symbol(path.root)
                .is_some_and(|symbol| symbol.name == name)
                .then_some(expression.id)
        })
        .unwrap()
}

#[test]
fn budget_and_unsupported_notices_are_suppressed() {
    with_context("template T(){}", |context| {
        for reason in [
            SummaryBlocker::ContextBudget,
            SummaryBlocker::RecursiveCycle,
            SummaryBlocker::UnsupportedContext,
            SummaryBlocker::ExternalSummary,
        ] {
            assert!(context.summary(&reason).is_empty(), "{reason:?}");
        }
        let entry = context.facts.unwrap().cfg().entry();
        let blockers = BTreeSet::from([FactBlocker::Budget(entry)]);
        assert!(context.rule(&AbstentionReason::LocalFacts(blockers)).is_empty());
    });
}

#[test]
fn missing_parameter_explanation_is_specific_and_excludes_unrelated_slots() {
    with_context("template T(n,m){var x=n;if(x){log(x);}}", |context| {
        let expression = access(context, "x");
        let result = context.rule(&AbstentionReason::LocalFacts(BTreeSet::from([
            FactBlocker::DeferredShape(expression),
        ])));
        assert_eq!(result.len(), 1, "{result:?}");
        assert_eq!(result[0].kind, CoverageKind::MissingContext);
        assert!(result[0].message.contains("`n`"));
        assert!(!result[0].message.contains("`m`"));
        assert!(result[0].help.contains("caller"));
        assert_eq!(result[0].span, context.hir.expression(expression).unwrap().span);
    });
}

#[test]
fn supplied_scalar_parameters_are_not_reported_as_missing() {
    with_context("template T(n){var x=n;log(x);}component main=T(7);", |context| {
        assert!(context.rule(&AbstentionReason::SymbolicParameters).is_empty());
        assert!(context
            .summary(&SummaryBlocker::UnprovenArgument(access(context, "x")))
            .is_empty());
    });
}

#[test]
fn ambiguous_local_dependencies_are_suppressed() {
    for source in [
        "template T(n,m){var x=n;if(0){x=m;}log(x);}",
        "template T(n){signal input in;var x=in;log(x);x=n;}",
        "template T(n){var x;var y;x=y;y=x;log(x);}",
    ] {
        with_context(source, |context| {
            let result = context.summary(&SummaryBlocker::UnprovenArgument(access(context, "x")));
            assert!(result.is_empty(), "{result:?}");
        });
    }
}

#[test]
fn vague_causes_and_duplicate_source_errors_are_suppressed() {
    with_context("template T(n){signal input in;log(in);}", |context| {
        for reason in [
            AbstentionReason::UnsupportedConstruct,
            AbstentionReason::IncompleteDefinition,
            AbstentionReason::LocalFacts(BTreeSet::from([FactBlocker::ExternalSummary])),
        ] {
            assert!(context.rule(&reason).is_empty());
        }
        assert!(context
            .summary(&SummaryBlocker::UnprovenArgument(access(context, "in")))
            .is_empty());
    });
}

#[test]
fn resource_limits_do_not_hide_actionable_context() {
    with_context("template T(n){var x=n;if(x){log(x);}}", |context| {
        let cfg = context.facts.unwrap().cfg();
        let branch = cfg
            .nodes()
            .iter()
            .find(|id| {
                let Some(CfgNodeKind::Branch { .. }) = cfg.node(**id).map(|node| &node.kind) else {
                    return false;
                };
                true
            })
            .copied()
            .unwrap();
        let result = context.rule(&AbstentionReason::LocalFacts(BTreeSet::from([
            FactBlocker::DeferredControl(branch),
            FactBlocker::Budget(branch),
        ])));
        assert_eq!(result.len(), 1, "{result:?}");
        let categories: BTreeSet<_> = result.iter().map(|item| item.kind).collect();
        assert_eq!(categories, BTreeSet::from([CoverageKind::MissingContext]));
        for item in &result {
            assert_eq!(item.span, cfg.node(branch).unwrap().origin.unwrap().span);
        }
        assert!(!result.iter().any(|item| item.help.contains("--")));
    });
}

#[test]
fn internal_errors_remain_distinct_from_missing_source_context() {
    with_context("template T(){}", |context| {
        let internal = context.summary(&SummaryBlocker::WrongContext);
        assert_eq!(internal[0].kind, CoverageKind::InternalError);
        assert!(internal[0].message.contains("analyzer"));
        assert!(internal[0].help.contains("Report"));
        assert!(context.summary(&SummaryBlocker::ForeignCall).is_empty());
    });
}

#[test]
fn unsupported_bus_context_is_not_a_user_action() {
    let lifted = fixture("pragma circom 2.2.3;bus B(){signal x;}template T(){}");
    let bus = &lifted.hir.buses()[0];
    let mut context =
        CoverageContext { hir: &lifted.hir, facts: None, evidence: None, span: bus.name_span };
    let result = context.summary(&SummaryBlocker::UnsupportedContext);
    assert!(result.is_empty());
    context.span = lifted.hir.templates()[0].name_span;
    assert!(context.summary(&SummaryBlocker::UnsupportedContext).is_empty());
}

#[test]
fn unsupported_template_context_is_not_a_user_action() {
    let lifted = fixture("template custom extern_c T(){}template U(){}");
    let mut context = CoverageContext {
        hir: &lifted.hir,
        facts: None,
        evidence: None,
        span: lifted.hir.templates()[0].name_span,
    };
    let result = context.summary(&SummaryBlocker::ExternalSummary);
    assert!(result.is_empty());
    context.span = lifted.hir.templates()[1].name_span;
    assert!(context.summary(&SummaryBlocker::ExternalSummary).is_empty());
}

#[test]
fn registered_signal_checks_do_not_blame_unrelated_symbolic_parameters() {
    let lifted = fixture("template T(n){signal input in;signal output out;out<==in+2;}");
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let rules = RuleContext::new(&facts, &provider, &evidence).unwrap();
    let result = run_registered(&rules).unwrap();
    assert!(result
        .abstentions()
        .iter()
        .any(|item| { item.reason == AbstentionReason::SymbolicParameters }));
    for abstention in result.abstentions() {
        let context = CoverageContext {
            hir: &lifted.hir,
            facts: Some(&facts),
            evidence: Some(&evidence),
            span: abstention.span,
        };
        assert!(context.rule(&abstention.reason).is_empty(), "{abstention:?}");
    }
}

#[test]
fn summary_node_indices_do_not_resolve_against_the_caller_cfg() {
    with_context("template T(n){if(n){log(n);}}template U(m){if(m){log(m);}}", |context| {
        let callee = build_cfg(context.hir, context.hir.definition("U").unwrap()).unwrap();
        let branch = callee
            .nodes()
            .iter()
            .copied()
            .find(|id| {
                let Some(CfgNodeKind::Branch { .. }) = callee.node(*id).map(|node| &node.kind)
                else {
                    return false;
                };
                true
            })
            .unwrap();
        let blockers = BTreeSet::from([FactBlocker::DeferredControl(branch)]);
        assert_eq!(context.rule(&AbstentionReason::LocalFacts(blockers.clone())).len(), 1);
        assert!(context.summary(&SummaryBlocker::LocalFacts(blockers)).is_empty());
        let budget = context
            .summary(&SummaryBlocker::LocalFacts(BTreeSet::from([FactBlocker::Budget(branch)])));
        assert!(budget.is_empty());
    });
}

#[test]
fn unsupported_owner_does_not_explain_an_unrelated_expression_blocker() {
    with_context("template custom T(n){var x=n;log(x);}", |context| {
        let expression = context.hir.expression(access(context, "x")).unwrap();
        let context = CoverageContext { span: expression.span, ..*context };
        assert!(context.rule(&AbstentionReason::UnsupportedConstruct).is_empty());
        assert!(context.summary(&SummaryBlocker::ExternalSummary).is_empty());
    });
}

#[test]
fn symbolic_expression_names_only_parameters_it_uses() {
    with_context("template T(n,m){log(n);}", |context| {
        let span = context.hir.expression(access(context, "n")).unwrap().span;
        let context = CoverageContext { span, ..*context };
        let result = context.rule(&AbstentionReason::SymbolicParameters);
        assert_eq!(result.len(), 1);
        assert!(result[0].message.contains("`n`"));
        assert!(!result[0].message.contains("`m`"));
    });
}
