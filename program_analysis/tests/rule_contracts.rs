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

use std::collections::BTreeSet;
use std::fs;

use abstract_interpretation::graph::NodeId;
use circomspect_program_analysis::rules::{
    constraints, maintainability, numeric, uses, AbstentionReason, RenderError, RuleContext,
    RuleContextError, RuleKind, RuleResult, ScopedAbstention, SourceMap,
};
use circomspect_program_analysis::hir_facts::{FactBlocker, FieldContext, Range};
use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::analyze;
use circomspect_program_analysis::interprocedural::{
    ArgumentValue, CallBlocker, CallOwner, CallReachability, ProjectOutputStatus, ProjectAnalysis,
    SummaryBlocker,
};
use parser::hir::lift_project;
use parser::frontend::{load_sources, SourceId, Span, Version, VersionPolicy};
use program_structure::report::{MessageCategory, Report};
use program_structure::report_code::ReportCode;
use program_structure::utils::constants::Curve;
use serde_json::Value;

fn load_fixture(name: &str, source: &str) -> parser::frontend::LoadedProject {
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

#[test]
fn rule_context_requires_matching_certified_scope() {
    let loaded = load_fixture("rule-context", "template First() {} template Second() {}\n");
    let lifted = lift_project(&loaded);
    let first = lifted.hir.definition("First").unwrap();
    let second = lifted.hir.definition("Second").unwrap();
    let cfg = build_cfg(&lifted.hir, first).unwrap();
    let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let first_root = summaries.contexts().symbolic_root(first).unwrap();
    let second_root = summaries.contexts().symbolic_root(second).unwrap();
    let facts = summaries.contexts().analyze_for_evidence(&cfg, &first_root, None).unwrap();
    let context = RuleContext::new(&facts, &summaries, &first_root).unwrap();
    assert_eq!(context.hir().identity(), lifted.hir.identity());
    assert_eq!(context.call_context(), first_root.context());
    assert_eq!(
        RuleContext::new(&facts, &summaries, &second_root).err(),
        Some(RuleContextError::WrongDefinition)
    );
    let gold = ProjectAnalysis::build(&lifted, Curve::Goldilocks).unwrap();
    let gold_root = gold.contexts().symbolic_root(first).unwrap();
    assert_eq!(
        RuleContext::new(&facts, &gold, &gold_root).err(),
        Some(RuleContextError::WrongCurve)
    );
    let foreign_loaded = load_fixture("foreign-context", "template First() {}\n");
    let foreign = lift_project(&foreign_loaded);
    let foreign_provider = ProjectAnalysis::build(&foreign, Curve::Bn254).unwrap();
    let foreign_root = foreign_provider
        .contexts()
        .symbolic_root(foreign.hir.definition("First").unwrap())
        .unwrap();
    assert_eq!(
        RuleContext::new(&facts, &foreign_provider, &foreign_root).err(),
        Some(RuleContextError::ForeignProject)
    );
    let gold_facts = gold.contexts().analyze_for_evidence(&cfg, &gold_root, None).unwrap();
    assert_eq!(
        RuleContext::new(&gold_facts, &summaries, &first_root).err(),
        Some(RuleContextError::WrongCurve)
    );
}

#[test]
fn concrete_rule_context_rejects_unbound_and_wrong_seed_facts() {
    let loaded = load_fixture(
        "rule-seed",
        "template Child(n){signal output y;if(n){y<==1;}else{y<==2;}} \
         template One(){component c=Child(1);} template Two(){component c=Child(0);}\n",
    );
    let lifted = lift_project(&loaded);
    let child = lifted.hir.definition("Child").unwrap();
    let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let mut child_evidence = Vec::new();
    for name in ["One", "Two"] {
        let parent = lifted.hir.definition(name).unwrap();
        let root = summaries.contexts().symbolic_root(parent).unwrap();
        let parent_cfg = build_cfg(&lifted.hir, parent).unwrap();
        let parent_facts =
            summaries.contexts().analyze_for_evidence(&parent_cfg, &root, None).unwrap();
        let site = summaries.graph().calls_from(CallOwner::Definition(parent))[0];
        let CallReachability::Reachable(call) =
            summaries.graph().reachable_call(site.id(), &parent_facts)
        else {
            panic!("checked child call")
        };
        child_evidence
            .push(summaries.contexts().call_evidence(&call, &parent_facts, &root).unwrap());
    }
    assert_eq!(child_evidence.len(), 2);
    assert_ne!(child_evidence[0].context(), child_evidence[1].context());
    let child_cfg = build_cfg(&lifted.hir, child).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let unbound = analyze(&lifted.hir, &child_cfg, &field, None).unwrap();
    assert_eq!(
        RuleContext::new(&unbound, &summaries, &child_evidence[0]).err(),
        Some(RuleContextError::MismatchedFacts(SummaryBlocker::WrongContext))
    );
    let seeded =
        summaries.contexts().analyze_for_evidence(&child_cfg, &child_evidence[0], None).unwrap();
    let scoped = RuleContext::new(&seeded, &summaries, &child_evidence[0]).unwrap();
    let parser::hir::DefinitionRef::Template(child_id) = child else { panic!("template") };
    let port = lifted.hir.template(child_id).unwrap().ports[0];
    let summary = scoped.template_port(port, &[]).unwrap();
    assert!(summary.unavailable().unwrap().contains(&SummaryBlocker::UnsupportedContext));
    let summary =
        summaries.templates().template_port_at(child_id, scoped.call_context(), port, &[]);
    let summary = summary.certified().unwrap();
    assert_eq!(summary.context(), child_evidence[0].context());
    assert_eq!(summary.fixed_value(), Some(&field.canonical(1.into())));
    assert_eq!(
        RuleContext::new(&seeded, &summaries, &child_evidence[1]).err(),
        Some(RuleContextError::MismatchedFacts(SummaryBlocker::WrongContext))
    );
    let other_facts =
        summaries.contexts().analyze_for_evidence(&child_cfg, &child_evidence[1], None).unwrap();
    let other = RuleContext::new(&other_facts, &summaries, &child_evidence[1]).unwrap();
    let other_summary = other.template_port(port, &[]).unwrap();
    assert!(other_summary.unavailable().unwrap().contains(&SummaryBlocker::UnsupportedContext));
    let other_summary =
        summaries.templates().template_port_at(child_id, other.call_context(), port, &[]);
    assert_eq!(other_summary.certified().unwrap().fixed_value(), Some(&field.canonical(2.into())));
    let symbolic = summaries.contexts().symbolic_root(child).unwrap();
    assert_eq!(
        RuleContext::new(&seeded, &summaries, &symbolic).err(),
        Some(RuleContextError::MismatchedFacts(SummaryBlocker::WrongContext))
    );
    let universal = summaries.contexts().analyze_for_evidence(&child_cfg, &symbolic, None).unwrap();
    assert!(RuleContext::new(&universal, &summaries, &symbolic).is_ok());
}

#[test]
fn function_summaries_are_bound_to_the_active_definition() {
    let loaded = load_fixture("function-scope", "function F(){return 1;}\n");
    let lifted = lift_project(&loaded);
    let definition = lifted.hir.definition("F").unwrap();
    let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = summaries.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = summaries.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &summaries, &evidence).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    assert_eq!(
        context.function_summary().unwrap().certified().unwrap().complete_return().unwrap(),
        &Range::Exact(field.canonical(1.into()))
    );
    assert!(context.function_effects().unwrap().certified().is_some());
}

#[test]
fn applied_component_port_uses_active_reachability_and_exact_instance() {
    let loaded = load_fixture(
        "component-scope",
        concat!(
            "template Child(n){signal output out;if(n){out<==1;}else{out<==0;}} ",
            "template Parent(){component c[2];c[0]=Child(0);c[1]=Child(1);} ",
            "template Other(){component c=Child(2);}"
        ),
    );
    let lifted = lift_project(&loaded);
    let parent = lifted.hir.definition("Parent").unwrap();
    let other = lifted.hir.definition("Other").unwrap();
    let parser::hir::DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap()
    else {
        panic!("Child is a template")
    };
    let output = lifted.hir.template(child).unwrap().ports[0];
    let parent_component = lifted
        .hir
        .components()
        .iter()
        .find(|component| lifted.hir.symbol(component.symbol).unwrap().name == "c")
        .unwrap()
        .id;
    let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = summaries.contexts().symbolic_root(parent).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = summaries.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &summaries, &evidence).unwrap();
    let sites = context.call_sites();
    assert_eq!(sites.len(), 2);
    assert!(sites.iter().all(|site| site.owner == CallOwner::Definition(parent)));
    let handles = [0, 1].map(|index| {
        context.facts().component_output_handle(parent_component, &[index], output, &[]).unwrap()
    });
    let field = FieldContext::for_curve(Curve::Bn254);
    for (index, expected) in [(0, 0), (1, 1)] {
        let applied = context.applied_component_port(sites[index].id(), &handles[index]).unwrap();
        let applied = applied.unwrap();
        let applied = applied.certified().unwrap_or_else(|| panic!("{:?}", applied.unavailable()));
        assert_eq!(applied.caller_evidence().context(), context.call_context());
        assert_eq!(applied.port_summary().fixed_value(), Some(&field.canonical(expected.into())));
    }
    let mismatched = context.applied_component_port(sites[0].id(), &handles[1]).unwrap().unwrap();
    assert!(mismatched.unavailable().unwrap().contains(&SummaryBlocker::WrongInstance));
    let foreign = summaries.graph().calls_from(CallOwner::Definition(other))[0].id();
    assert_eq!(
        context.applied_component_port(foreign, &handles[0]).err(),
        Some(CallBlocker::ForeignDefinition)
    );
}

#[test]
fn unreachable_component_call_has_no_applied_port_fact() {
    let loaded = load_fixture(
        "unreachable-component",
        concat!(
            "template Child(){signal output out;out<==1;} ",
            "template Parent(){component c;if(0){c=Child();}}"
        ),
    );
    let lifted = lift_project(&loaded);
    let parent = lifted.hir.definition("Parent").unwrap();
    let parser::hir::DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap()
    else {
        panic!("Child is a template")
    };
    let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = summaries.contexts().symbolic_root(parent).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = summaries.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &summaries, &evidence).unwrap();
    let sites = context.call_sites();
    assert_eq!(sites.len(), 1);
    let handle = context
        .facts()
        .component_output_handle(
            lifted.hir.components()[0].id,
            &[],
            lifted.hir.template(child).unwrap().ports[0],
            &[],
        )
        .unwrap();
    assert!(context.applied_component_port(sites[0].id(), &handle).unwrap().is_none());
}

#[test]
fn exact_caller_output_read_does_not_certify_an_unused_sibling() {
    let loaded = load_fixture(
        "output-read-scope",
        concat!(
            "template Child(){signal output out;out<==1;} ",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
            "signal output y;y<==c[0].out+1;}"
        ),
    );
    let lifted = lift_project(&loaded);
    let parent = lifted.hir.definition("Parent").unwrap();
    let parser::hir::DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap()
    else {
        panic!("Child is a template")
    };
    let output = lifted.hir.template(child).unwrap().ports[0];
    let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = summaries.contexts().symbolic_root(parent).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = summaries.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &summaries, &evidence).unwrap();
    let sites = context.call_sites();
    assert_eq!(sites.len(), 2);
    for (index, site) in sites.iter().enumerate() {
        let handle = context
            .facts()
            .component_output_handle(lifted.hir.components()[0].id, &[index], output, &[])
            .unwrap();
        let applied = context.applied_component_port(site.id(), &handle).unwrap().unwrap();
        let project_use = context.closed_project_output_uses();
        assert!(project_use.certified().is_none());
        let read = context.caller_output_read(applied.certified().unwrap()).unwrap();
        if index == 0 {
            assert_eq!(read.certified().unwrap().read_origins().len(), 1);
        } else {
            assert!(read.certified().is_none());
            assert!(read.unavailable().unwrap().contains(&SummaryBlocker::ExternalSummary));
        }
    }
}

#[test]
fn main_rule_context_exposes_exact_project_output_use() {
    let loaded = load_fixture(
        "main-output-use",
        concat!(
            "template Child(){signal output out;out<==1;} ",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
            "signal output y;y<==c[0].out+1;} component main=Parent();"
        ),
    );
    let lifted = lift_project(&loaded);
    let parent = lifted.hir.definition("Parent").unwrap();
    let parser::hir::DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap()
    else {
        panic!("Child is a template")
    };
    let parser::hir::DefinitionRef::Template(parent_template) = parent else {
        panic!("Parent is a template")
    };
    let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let main = summaries.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        summaries.graph().reachable_main_call(main.id(), &lifted.hir)
    else {
        panic!("main resolves to Parent")
    };
    let evidence = summaries.contexts().main_evidence(&main).unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = summaries.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &summaries, &evidence).unwrap();
    let output = lifted.hir.template(child).unwrap().ports[0];
    let statuses = [ProjectOutputStatus::Read, ProjectOutputStatus::Unused];
    let project_uses = context.closed_project_output_uses();
    let project_uses = project_uses.certified().unwrap();
    let sites = context.call_sites();
    assert_eq!(sites.len(), statuses.len());
    for (index, site) in sites.iter().enumerate() {
        let handle = facts
            .component_output_handle(lifted.hir.components()[0].id, &[index], output, &[])
            .unwrap();
        let applied = context.applied_component_port(site.id(), &handle).unwrap().unwrap();
        let result = project_uses
            .iter()
            .find(|proof| proof.handle() == applied.certified().unwrap().handle())
            .unwrap();
        assert_eq!(result.status(), statuses[index]);
        assert_eq!(result.handle(), &handle);
        assert_eq!(result.main_evidence(), &evidence);
    }
    let output = lifted.hir.template(parent_template).unwrap().ports[0];
    let handle = facts.port_handle(output, &[]).unwrap();
    let exported = context.exported_main_output_use(&handle);
    assert_eq!(exported.certified().unwrap().status(), ProjectOutputStatus::Read);
    assert_eq!(exported.certified().unwrap().handle(), &handle);

    let symbolic = summaries.contexts().symbolic_root(parent).unwrap();
    let symbolic_facts = summaries.contexts().analyze_for_evidence(&cfg, &symbolic, None).unwrap();
    let symbolic_context = RuleContext::new(&symbolic_facts, &summaries, &symbolic).unwrap();
    let symbolic_handle = symbolic_facts.port_handle(output, &[]).unwrap();
    assert!(symbolic_context.exported_main_output_use(&symbolic_handle).certified().is_none());
}

#[test]
fn composed_output_constraint_requires_the_active_caller_scope() {
    let loaded = load_fixture(
        "composed-output-scope",
        concat!(
            "template Child(){signal input in;signal output out;out<==in;} ",
            "template Parent(){component c=Child();c.in<==7;} ",
            "template Other(){component c=Child();c.in<--8;}"
        ),
    );
    let lifted = lift_project(&loaded);
    let parent = lifted.hir.definition("Parent").unwrap();
    let other = lifted.hir.definition("Other").unwrap();
    let parser::hir::DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap()
    else {
        panic!("Child is a template")
    };
    let output = lifted.hir.template(child).unwrap().ports[1];
    let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let parent_evidence = summaries.contexts().symbolic_root(parent).unwrap();
    let parent_cfg = build_cfg(&lifted.hir, parent).unwrap();
    let parent_facts =
        summaries.contexts().analyze_for_evidence(&parent_cfg, &parent_evidence, None).unwrap();
    let parent_context = RuleContext::new(&parent_facts, &summaries, &parent_evidence).unwrap();
    let handle = parent_context
        .facts()
        .component_output_handle(lifted.hir.components()[0].id, &[], output, &[])
        .unwrap();
    let site = parent_context.call_sites()[0].id();
    let applied = parent_context.applied_component_port(site, &handle).unwrap().unwrap();
    let applied = applied.certified().unwrap();
    let composed = parent_context.composed_constraint_fixed_output(applied).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    assert_eq!(composed.certified().unwrap().value(), &field.canonical(7.into()));

    let other_evidence = summaries.contexts().symbolic_root(other).unwrap();
    let other_cfg = build_cfg(&lifted.hir, other).unwrap();
    let other_facts =
        summaries.contexts().analyze_for_evidence(&other_cfg, &other_evidence, None).unwrap();
    let other_context = RuleContext::new(&other_facts, &summaries, &other_evidence).unwrap();
    assert_eq!(
        other_context.composed_constraint_fixed_output(applied).err(),
        Some(SummaryBlocker::WrongContext)
    );
    assert_eq!(other_context.caller_output_read(applied).err(), Some(SummaryBlocker::WrongContext));
    assert_eq!(other_context.closed_project_output_uses().certified(), None);
    let other_handle = other_context
        .facts()
        .component_output_handle(lifted.hir.components()[1].id, &[], output, &[])
        .unwrap();
    let other_site = other_context.call_sites()[0].id();
    let other_applied =
        other_context.applied_component_port(other_site, &other_handle).unwrap().unwrap();
    let other_composed =
        other_context.composed_constraint_fixed_output(other_applied.certified().unwrap()).unwrap();
    assert!(other_composed.unavailable().is_some());
}

#[test]
fn diagnostic_names_shared_family_and_retired_ids_are_stable() {
    let incomplete = RuleKind::IncompleteCoverage;
    assert_eq!(incomplete.code().name(), "incomplete-analysis");
    let redundant = RuleKind::RedundantWitnessAssignment;
    assert_eq!(redundant.code().name(), "redundant-witness-assignment");
    assert_eq!(RuleKind::BitwiseComplement.code().id(), RuleKind::FieldArithmetic.code().id());
    assert_eq!(RuleKind::BitwiseComplement.code().name(), "field-element-arithmetic");
    let ids: Vec<_> = circomspect_program_analysis::rules::registered_rules()
        .map(|rule| rule.kind().code().id())
        .collect();
    assert!(!ids.iter().any(|id| id == "CS0013" || id == "CS0017"));
}

#[test]
fn every_rule_kind_has_a_frozen_id_and_level() {
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
        (SignalDependentAssert, "CS0023", MessageCategory::Warning),
        (UnassignedOutput, "CS0024", MessageCategory::Warning),
        (ComparatorPrecondition, "CS0025", MessageCategory::Warning),
        (UnusedPublicInput, "CS0026", MessageCategory::Warning),
        (AlternateWitnessValue, "CS0027", MessageCategory::Warning),
        (NonInjectiveBitPacking, "CS0028", MessageCategory::Warning),
        (FeasibleZeroDivisor, "CS0029", MessageCategory::Warning),
        (UnprovedBinaryTag, "CS0030", MessageCategory::Warning),
    ];
    for (kind, id, level) in expected {
        assert_eq!(kind.code().id(), id, "{kind:?}");
        assert_eq!(kind.category(), level, "{kind:?}");
    }
}

#[test]
fn rule_families_partition_the_planned_rules() {
    let families = [numeric::KINDS, constraints::KINDS, uses::KINDS, maintainability::KINDS];
    let mut kinds = BTreeSet::new();
    for family in families {
        for kind in family {
            assert!(kinds.insert(*kind), "duplicate rule kind: {kind:?}");
        }
    }
    assert_eq!(kinds.len(), 25);
    assert!(!kinds.contains(&RuleKind::IncompleteCoverage));
    assert!(kinds.contains(&RuleKind::UnconstrainedSignal));
    assert!(kinds.contains(&RuleKind::UnusedVariableValue));
    assert!(kinds.contains(&RuleKind::UnusedParameterValue));
}

#[test]
fn abstention_keeps_an_unproved_predicate_out_of_reports() {
    let loaded = load_fixture("abstain", "template Check(n) { signal output y; y <-- n; }\n");
    let lifted = lift_project(&loaded);
    let definition = lifted.hir.definition("Check").unwrap();
    let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let context = summaries.contexts().symbolic_context_for(definition).unwrap();
    let symbolic_context = context.clone();
    let source = &loaded.files[0];
    let span = Span::checked(source.id, 0..8, &source.text).unwrap();
    let sources = SourceMap::from_loaded(&loaded, &[source.id]).unwrap();
    let mut result = RuleResult::default();
    result.add_abstention(ScopedAbstention {
        kind: RuleKind::UnconstrainedSignal,
        context,
        span,
        reason: AbstentionReason::SymbolicParameters,
    });
    assert!(result.findings().is_empty());
    assert_eq!(result.abstentions().len(), 1);
    assert_eq!(result.abstentions()[0].definition(), definition);
    let field = FieldContext::for_curve(Curve::Bn254);
    let one = summaries
        .contexts()
        .context_for(definition, vec![ArgumentValue::Scalar(field.canonical(1.into()))])
        .unwrap();
    let two = summaries
        .contexts()
        .context_for(definition, vec![ArgumentValue::Scalar(field.canonical(2.into()))])
        .unwrap();
    assert_ne!(one, two);
    result.add_abstention(ScopedAbstention {
        kind: RuleKind::UnconstrainedSignal,
        context: one,
        span,
        reason: AbstentionReason::SymbolicParameters,
    });
    result.add_abstention(ScopedAbstention {
        kind: RuleKind::UnconstrainedSignal,
        context: two,
        span,
        reason: AbstentionReason::SymbolicParameters,
    });
    assert_eq!(result.abstentions().len(), 3);
    assert_ne!(result.abstentions()[1].context, result.abstentions()[2].context);
    let local_blockers = BTreeSet::from([
        FactBlocker::Budget(NodeId::new(2)),
        FactBlocker::OpaqueNode(NodeId::new(3), "missing call".to_string()),
    ]);
    let summary_blockers =
        BTreeSet::from([SummaryBlocker::ContextBudget, SummaryBlocker::ExternalSummary]);
    let call_context = symbolic_context.clone();
    result.add_abstention(ScopedAbstention {
        kind: RuleKind::UnconstrainedSignal,
        context: symbolic_context.clone(),
        span,
        reason: AbstentionReason::LocalFacts(local_blockers.clone()),
    });
    result.add_abstention(ScopedAbstention {
        kind: RuleKind::UnconstrainedSignal,
        context: symbolic_context,
        span,
        reason: AbstentionReason::Summary(summary_blockers.clone()),
    });
    let call_blockers = BTreeSet::from([
        CallBlocker::UnresolvedTarget,
        CallBlocker::LocalFacts(BTreeSet::from([FactBlocker::Budget(NodeId::new(4))])),
    ]);
    result.add_abstention(ScopedAbstention {
        kind: RuleKind::UnconstrainedSignal,
        context: call_context,
        span,
        reason: AbstentionReason::Call(call_blockers.clone()),
    });
    assert_eq!(result.abstentions().len(), 6);
    assert_eq!(result.abstentions()[3].reason, AbstentionReason::LocalFacts(local_blockers));
    assert_eq!(result.abstentions()[4].reason, AbstentionReason::Summary(summary_blockers));
    assert_eq!(result.abstentions()[5].reason, AbstentionReason::Call(call_blockers));
    let output = source.path.with_extension("sarif.json");
    assert_eq!(
        support::render(result.findings(), &sources, MessageCategory::Info, &[], &output).unwrap(),
        (0, 0)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
    assert_eq!(sarif["runs"][0]["results"].as_array().unwrap().len(), 0);
}

#[test]
fn validated_findings_render_with_fixed_ids_spans_and_filters() {
    let loaded = load_fixture("finding-render", "template Check() {}\n");
    let lifted = lift_project(&loaded);
    let definition = lifted.hir.definition("Check").unwrap();
    let parser::hir::DefinitionRef::Template(template) = definition else {
        panic!("Check is a template")
    };
    let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let evidence = summaries.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = summaries.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let context = RuleContext::new(&facts, &summaries, &evidence).unwrap();
    let source = &loaded.files[0];
    let primary = lifted.hir.template(template).unwrap().name_span;
    let secondary = Span::checked(source.id, 0..8, &source.text).unwrap();
    let warning = context
        .finding(RuleKind::TooManyArguments, "proved warning".into(), primary, "name".into())
        .with_secondary(secondary, "declaration".into());
    let note =
        context.finding(RuleKind::FieldArithmetic, "proved note".into(), primary, "name".into());
    let sources = SourceMap::from_loaded(&loaded, &[source.id]).unwrap();
    let output = source.path.with_extension("sarif.json");

    assert_eq!(
        support::render(
            &[warning.clone(), note.clone()],
            &sources,
            MessageCategory::Warning,
            &[],
            &output
        )
        .unwrap(),
        (1, 1)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
    let results = sarif["runs"][0]["results"].as_array().unwrap();
    assert_eq!(results.len(), 1);
    assert_eq!(results[0]["ruleId"], "CS0012");
    assert_eq!(results[0]["level"], "warning");
    assert_eq!(results[0]["locations"][0]["physicalLocation"]["region"]["startLine"], 1);
    assert_eq!(results[0]["locations"][0]["physicalLocation"]["region"]["startColumn"], 10);
    assert_eq!(results[0]["locations"][0]["physicalLocation"]["region"]["endColumn"], 15);
    assert_eq!(results[0]["relatedLocations"][0]["physicalLocation"]["region"]["startColumn"], 1);
    assert_eq!(results[0]["relatedLocations"][0]["physicalLocation"]["region"]["endColumn"], 9);

    assert_eq!(
        support::render(&[warning, note], &sources, MessageCategory::Info, &["CS0012"], &output)
            .unwrap(),
        (1, 1)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
    let results = sarif["runs"][0]["results"].as_array().unwrap();
    assert_eq!(results.len(), 1);
    assert_eq!(results[0]["ruleId"], "CS0004");
    assert_eq!(results[0]["level"], "note");

    let ordered = [
        context.finding(RuleKind::FieldArithmetic, "proved note".into(), primary, "name".into()),
        context.finding(
            RuleKind::TooManyArguments,
            "proved warning".into(),
            primary,
            "name".into(),
        ),
    ];
    assert_eq!(
        support::render(&ordered, &sources, MessageCategory::Info, &[], &output).unwrap(),
        (2, 2)
    );
    let first = fs::read_to_string(&output).unwrap();
    let sarif: Value = serde_json::from_str(&first).unwrap();
    let results = sarif["runs"][0]["results"].as_array().unwrap();
    assert_eq!(
        results.iter().map(|result| result["ruleId"].as_str().unwrap()).collect::<Vec<_>>(),
        ["CS0004", "CS0012"]
    );
    let descriptors = sarif["runs"][0]["tool"]["driver"]["rules"].as_array().unwrap();
    assert_eq!(
        descriptors.iter().map(|rule| rule["id"].as_str().unwrap()).collect::<Vec<_>>(),
        ["CS0004", "CS0012"]
    );
    assert_eq!(
        support::render(&ordered, &sources, MessageCategory::Info, &[], &output).unwrap(),
        (2, 2)
    );
    let second = fs::read_to_string(&output).unwrap();
    let repeated: Value = serde_json::from_str(&second).unwrap();
    assert_eq!(repeated["runs"][0]["results"], sarif["runs"][0]["results"]);
    assert_eq!(second, first);
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
    let root_file = sources.file_id(root.id).unwrap();
    let included_file = sources.file_id(included.id).unwrap();
    let mut warning =
        Report::warning("proved property".to_string(), RuleKind::TooManyArguments.code());
    warning.add_primary(root_span.start()..root_span.end(), root_file, "evidence".to_string());
    warning.add_secondary(0..8, included_file, Some("related".to_string()));
    let mut note = Report::info("proved property".to_string(), RuleKind::FieldArithmetic.code());
    note.add_primary(root_span.start()..root_span.end(), root_file, "evidence".to_string());
    let mut hidden =
        Report::warning("proved property".to_string(), RuleKind::UnconstrainedDivision.code());
    hidden.add_primary(
        included_span.start()..included_span.end(),
        included_file,
        "evidence".to_string(),
    );
    let mut error = Report::error("missing function".to_string(), ReportCode::UndefinedFunction);
    error.add_primary(
        included_span.start()..included_span.end(),
        included_file,
        "call".to_string(),
    );
    let reports = [warning, note, hidden, error];
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
    assert_eq!(results[0]["relatedLocations"][0]["physicalLocation"]["region"]["startColumn"], 1);
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
fn unknown_roots_and_duplicate_sources_fail_before_rendering() {
    let loaded = load_fixture("invalid-source", "template Check() {}\n");
    let source = &loaded.files[0];
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
}

#[test]
fn registered_rule_order_matches_each_declared_family() {
    let declared: Vec<_> =
        [numeric::KINDS, constraints::KINDS, uses::KINDS, maintainability::KINDS]
            .into_iter()
            .flatten()
            .copied()
            .collect();
    let registered: Vec<_> = circomspect_program_analysis::rules::registered_rules()
        .map(circomspect_program_analysis::rules::Rule::kind)
        .collect();
    assert_eq!(registered, declared);
}

#[test]
fn rule_guards_preserve_complete_findings_and_abstentions() {
    let cases = [
        ("partial-body", "template Check(a,b,c,d,e,f,g,h){var value=Missing();}"),
        ("failed-function", "function Check(a,b,c,d,e,f,g,h){assert(0);return 0;}"),
        ("bus", "bus Check(){signal x;}"),
        ("witness", "template Check(){signal output y;y<--1;}"),
    ];
    let mut records = Vec::new();
    for (name, source) in cases {
        records.push(format!("CASE {name}"));
        let loaded = load_fixture(name, source);
        let lifted = lift_project(&loaded);
        let definition = lifted.hir.definition("Check").unwrap();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let evidence = summaries.contexts().symbolic_root(definition).unwrap();
        let facts = summaries.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let context = RuleContext::new(&facts, &summaries, &evidence).unwrap();
        let result = circomspect_program_analysis::rules::run_registered(&context).unwrap();
        let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
        for finding in result.findings() {
            assert_eq!(finding.context(), context.call_context());
            let report = finding.to_report(&sources).unwrap();
            records.push(format!(
                "F {:?} {:?} {:?} {:?}",
                finding.kind(),
                report.message(),
                report.primary(),
                report.secondary()
            ));
        }
        for abstention in result.abstentions() {
            assert_eq!(&abstention.context, context.call_context());
            records.push(format!(
                "A {:?} {}..{} {:?}",
                abstention.kind,
                abstention.span.start(),
                abstention.span.end(),
                abstention.reason
            ));
        }
    }
    let fingerprint = records.join("\n") + "\n";
    assert_eq!(fingerprint, include_str!("fixtures/rule_guard_contract.txt"));
}
