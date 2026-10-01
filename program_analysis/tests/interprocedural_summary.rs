use circomspect_program_analysis::hir_facts::{FieldContext, Incidence, Range};
use circomspect_program_analysis::interprocedural::{
    ArgumentValue, FunctionEffect, ProjectSummaries, SummaryBlocker, WitnessProvenance,
};
use parser::hir::{lower_project, DefinitionRef, Effect, ExprKind, LoweredProject};
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

#[test]
fn direct_resolved_function_call_agrees_with_inlined_return() {
    let lowered = fixture("function Id(a){return a;} function Outer(n){return Id(n);}");
    let provider = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let DefinitionRef::Function(outer) = lowered.hir.definition("Outer").unwrap() else {
        panic!("function Outer")
    };
    let body = lowered.hir.block(lowered.hir.function(outer).unwrap().body).unwrap();
    let Some(Effect::Return { value, .. }) = body.effects.first() else { panic!("Outer return") };
    let expression = lowered.hir.expression(*value).unwrap();
    assert!(matches!(expression.kind, ExprKind::Call { .. }), "{:?}", expression.kind);
    let field = FieldContext::for_curve(Curve::Bn254);
    let context = provider
        .context_for(
            DefinitionRef::Function(outer),
            vec![ArgumentValue::Scalar(field.canonical(5.into()))],
        )
        .unwrap();
    let summary = provider.function(outer, &context);
    assert_eq!(summary.certified().unwrap().returns(), &Range::Exact(field.canonical(5.into())));
    assert_eq!(
        summary.certified().unwrap().input_dependencies(),
        &std::collections::BTreeSet::from([0])
    );
}

#[test]
fn finite_recursive_contexts_reach_a_base_case_without_certifying_a_cycle() {
    let lowered = fixture("function F(n){if(n){return F(n-1);}return 0;}");
    let provider = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let DefinitionRef::Function(function) = lowered.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let field = FieldContext::for_curve(Curve::Bn254);
    let concrete = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Scalar(field.canonical(3.into()))],
        )
        .unwrap();
    let summary = provider.function(function, &concrete);
    assert_eq!(
        summary.certified().map(|item| item.returns()),
        Some(&Range::Exact(field.canonical(0.into()))),
        "{:?}",
        summary.unavailable()
    );
    let too_deep = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Scalar(field.canonical(70.into()))],
        )
        .unwrap();
    assert_eq!(
        provider.function(function, &too_deep).unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::ContextBudget]))
    );

    let cyclic = fixture("function F(n){return F(n);}");
    let cyclic_provider = ProjectSummaries::build(&cyclic, Curve::Bn254).unwrap();
    let DefinitionRef::Function(cyclic_id) = cyclic.hir.definition("F").unwrap() else {
        panic!("cyclic F")
    };
    let context = cyclic_provider
        .context_for(
            DefinitionRef::Function(cyclic_id),
            vec![ArgumentValue::Scalar(field.canonical(1.into()))],
        )
        .unwrap();
    assert_eq!(
        cyclic_provider.function(cyclic_id, &context).unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::RecursiveCycle]))
    );
}

#[test]
fn recursive_scc_effects_reach_a_least_fixed_point() {
    let lowered = fixture(
        "function F(n){if(n){return G(n);}return 0;} \
         function G(n){log(n);if(n){return F(n);}return 0;}",
    );
    let provider = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let DefinitionRef::Function(f) = lowered.hir.definition("F").unwrap() else { panic!("F") };
    let DefinitionRef::Function(g) = lowered.hir.definition("G").unwrap() else { panic!("G") };
    let field = FieldContext::for_curve(Curve::Bn254);
    let one = ArgumentValue::Scalar(field.canonical(1.into()));
    let f_one = provider.context_for(DefinitionRef::Function(f), vec![one.clone()]).unwrap();
    let g_one = provider.context_for(DefinitionRef::Function(g), vec![one]).unwrap();
    assert!(provider
        .function_effects(f, &f_one)
        .certified()
        .unwrap()
        .contains(FunctionEffect::Log));
    assert!(provider
        .function_effects(g, &g_one)
        .certified()
        .unwrap()
        .contains(FunctionEffect::Log));
    assert_eq!(
        provider.function(f, &f_one).unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::RecursiveCycle]))
    );
    let f_zero = provider
        .context_for(
            DefinitionRef::Function(f),
            vec![ArgumentValue::Scalar(field.canonical(0.into()))],
        )
        .unwrap();
    assert!(!provider
        .function_effects(f, &f_zero)
        .certified()
        .unwrap()
        .contains(FunctionEffect::Log));
}

#[test]
fn unreachable_and_unrelated_opaque_calls_do_not_invent_effects() {
    let lowered = fixture(
        "function G(){log(1);return 1;} \
         function Clean(){if(0){return G();}return 1;} \
         function Broken(){return Missing();}",
    );
    let provider = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let DefinitionRef::Function(clean) = lowered.hir.definition("Clean").unwrap() else {
        panic!("Clean")
    };
    let DefinitionRef::Function(broken) = lowered.hir.definition("Broken").unwrap() else {
        panic!("Broken")
    };
    let clean_context = provider.symbolic_context_for(DefinitionRef::Function(clean)).unwrap();
    let broken_context = provider.symbolic_context_for(DefinitionRef::Function(broken)).unwrap();
    let clean_effects = provider.function_effects(clean, &clean_context);
    assert!(!clean_effects.certified().unwrap().contains(FunctionEffect::Log));
    assert!(provider.function_effects(broken, &broken_context).unavailable().is_some());
    assert_eq!(
        provider.function(clean, &clean_context).certified().unwrap().returns(),
        &Range::Exact(FieldContext::for_curve(Curve::Bn254).canonical(1.into()))
    );
}

#[test]
fn template_port_summary_specializes_constraint_provenance() {
    let lowered = fixture("template T(n){signal output x;if(n){x<==1;}else{x<--1;}}");
    let provider = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let DefinitionRef::Template(template) = lowered.hir.definition("T").unwrap() else {
        panic!("template T")
    };
    let port = lowered.hir.template(template).unwrap().ports[0];
    let field = FieldContext::for_curve(Curve::Bn254);
    let one = provider
        .context_for(
            DefinitionRef::Template(template),
            vec![ArgumentValue::Scalar(field.canonical(1.into()))],
        )
        .unwrap();
    let zero = provider
        .context_for(
            DefinitionRef::Template(template),
            vec![ArgumentValue::Scalar(field.canonical(0.into()))],
        )
        .unwrap();
    let symbolic = provider.symbolic_context_for(DefinitionRef::Template(template)).unwrap();
    let constrained = provider.template_port(template, &one, port);
    assert_eq!(constrained.certified().unwrap().incidence(), Incidence::Must);
    assert_eq!(constrained.certified().unwrap().fixed_value(), Some(&field.canonical(1.into())));
    assert_eq!(
        provider.template_port(template, &zero, port).certified().unwrap().incidence(),
        Incidence::Zero
    );
    assert!(provider.template_port(template, &symbolic, port).unavailable().is_some());
    assert!(lowered.hir.mains().is_empty());
}

#[test]
fn template_port_summary_keeps_witness_and_read_evidence_separate() {
    let lowered = fixture("template T(){signal input x;signal output y,z;y<--x;z<==1;}");
    let provider = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let DefinitionRef::Template(template) = lowered.hir.definition("T").unwrap() else {
        panic!("template T")
    };
    let ports = &lowered.hir.template(template).unwrap().ports;
    let context = provider.symbolic_context_for(DefinitionRef::Template(template)).unwrap();
    assert_eq!(provider.template_port_read(template, &context, ports[0]).certified(), Some(&true));
    assert_eq!(
        provider.template_port_witnesses(template, &context, ports[1]).certified().map(Vec::len),
        Some(1)
    );
    assert_eq!(
        provider.template_port_witnesses(template, &context, ports[1]).certified().unwrap()[0]
            .provenance(),
        WitnessProvenance::WitnessOnly
    );
    assert_eq!(
        provider.template_port(template, &context, ports[1]).certified().unwrap().incidence(),
        Incidence::Zero
    );
    assert_eq!(
        provider.template_port_witnesses(template, &context, ports[2]).certified().map(Vec::len),
        Some(1)
    );
    assert_eq!(
        provider.template_port_witnesses(template, &context, ports[2]).certified().unwrap()[0]
            .provenance(),
        WitnessProvenance::GeneratedConstraint
    );
    assert_eq!(
        provider.template_port(template, &context, ports[2]).certified().unwrap().incidence(),
        Incidence::Must
    );
}

#[test]
fn opaque_witness_write_cannot_certify_an_empty_witness_summary() {
    let lowered = fixture("template T(){signal output y;y<--Missing();}");
    let provider = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let DefinitionRef::Template(template) = lowered.hir.definition("T").unwrap() else {
        panic!("template T")
    };
    let port = lowered.hir.template(template).unwrap().ports[0];
    let context = provider.symbolic_context_for(DefinitionRef::Template(template)).unwrap();
    assert!(provider.template_port_witnesses(template, &context, port).unavailable().is_some());
}

#[test]
fn exact_array_port_summaries_retain_distinct_element_identity() {
    let lowered = fixture("template T(){signal output out[2];out[0]<==1;out[1]<--2;}");
    let provider = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let DefinitionRef::Template(template) = lowered.hir.definition("T").unwrap() else {
        panic!("template T")
    };
    let port = lowered.hir.template(template).unwrap().ports[0];
    let context = provider.symbolic_context_for(DefinitionRef::Template(template)).unwrap();
    let first = provider.template_port_at(template, &context, port, &[0]);
    let second = provider.template_port_at(template, &context, port, &[1]);
    assert_eq!(first.certified().unwrap().indices(), [0]);
    assert_eq!(second.certified().unwrap().indices(), [1]);
    assert_eq!(first.certified().unwrap().incidence(), Incidence::Must);
    assert_eq!(second.certified().unwrap().incidence(), Incidence::Zero);
}
