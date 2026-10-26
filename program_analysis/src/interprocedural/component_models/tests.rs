use std::collections::BTreeMap;
use std::fs;

use parser::hir::{lift_project, DefinitionRef};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::build_cfg;
use crate::hir_facts::{analyze_with_scalar_parameters, FieldContext, ProofBudget};
use crate::interprocedural::component_models::{checked_bit_port_handles, RequestedBits};
use crate::interprocedural::{CallOwner, CallReachability, ProjectSummaries, SummaryBlocker};

#[test]
fn checked_port_candidates_use_the_selected_child_parameter_shape_and_roles() {
    let directory =
        std::env::temp_dir().join(format!("component-model-ports-{}", std::process::id()));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(
        &path,
        "template Child(n){signal input in;signal output bits[n];signal output scalar;}\
         component main=Child(2);",
    )
    .unwrap();
    let project = lift_project(&load_sources(
        &[path],
        &[directory],
        VersionPolicy::new(Version::new(2, 2, 3)),
    ));
    let provider = ProjectSummaries::build(&project, Curve::Goldilocks).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &project.hir)
    else {
        panic!("main call");
    };
    let evidence = provider.main_evidence(&call).unwrap();
    let definition = project.hir.definition("Child").unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let DefinitionRef::Template(id) = definition else { panic!("child template") };
    let ports = &project.hir.template(id).unwrap().ports;
    let (input, bits) = checked_bit_port_handles(&facts, ports[0], ports[1]).unwrap();
    assert_eq!(bits.len(), 2);
    assert_eq!(input.span(), project.hir.port(ports[0]).unwrap().span);
    assert!(checked_bit_port_handles(&facts, ports[1], ports[0]).is_err());
    assert!(checked_bit_port_handles(&facts, ports[0], ports[2]).is_err());

    let symbolic = provider.symbolic_root(definition).unwrap();
    let unknown = provider.analyze_for_evidence(&cfg, &symbolic, None).unwrap();
    assert!(checked_bit_port_handles(&unknown, ports[0], ports[1]).is_err());

    let parameter = project.hir.symbols().iter().find(|symbol| symbol.name == "n").unwrap().id;
    let field = FieldContext::for_curve(Curve::Goldilocks);
    let seeds = BTreeMap::from([(parameter, field.canonical(513.into()))]);
    let oversized =
        analyze_with_scalar_parameters(&project.hir, &cfg, &field, seeds, None).unwrap();
    assert_eq!(
        checked_bit_port_handles(&oversized, ports[0], ports[1]).unwrap_err(),
        SummaryBlocker::ContextBudget
    );
}

#[test]
fn closure_collection_charges_shared_site_term_key_and_operation_budgets() {
    let directory =
        std::env::temp_dir().join(format!("component-model-budget-{}", std::process::id()));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(
        &path,
        "template Child(){signal input in;signal output bit;bit<--0;\
        bit*(bit-1)===0;in===bit;}template Parent(){component c=Child();c.in<==0;}\
        component main=Parent();",
    )
    .unwrap();
    let project = lift_project(&load_sources(
        &[path],
        &[directory],
        VersionPolicy::new(Version::new(2, 2, 3)),
    ));
    let provider = ProjectSummaries::build(&project, Curve::Goldilocks).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &project.hir)
    else {
        panic!("main call")
    };
    let caller = provider.main_evidence(&call).unwrap();
    let parent = project.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&project.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("child call")
    };
    let callee = provider.call_evidence(&call, &facts, &caller).unwrap();
    let cfg = build_cfg(&project.hir, call.callee()).unwrap();
    let child = provider.analyze_for_evidence(&cfg, &callee, None).unwrap();
    let DefinitionRef::Template(id) = call.callee() else { panic!("child template") };
    let ports = &project.hir.template(id).unwrap().ports;
    let input = child.port_handle(ports[0], &[]).unwrap();
    let bit = child.port_handle(ports[1], &[]).unwrap();
    let applied = provider.apply_component_local_output(&facts, &caller, &call, &bit);
    let applied = applied.certified().unwrap();
    let bits = [bit];
    for (sites, terms, keys, operations) in
        [(0, 1000, 1000, 1000), (1000, 0, 1000, 1000), (1000, 1000, 0, 1000), (1000, 1000, 1000, 0)]
    {
        let result = provider.component_ambiguity_result(
            &facts,
            applied,
            RequestedBits::Handles { input: &input, bits: &bits },
            &mut ProofBudget::limited(sites, terms, keys, operations),
        );
        assert!(result.is_err(), "budget {sites}/{terms}/{keys}/{operations}: {result:?}");
    }
    let result = provider.component_ambiguity_result(
        &facts,
        applied,
        RequestedBits::Handles { input: &input, bits: &bits },
        &mut ProofBudget::default(),
    );
    assert!(result.is_ok(), "{result:?}");
}

#[test]
fn checked_port_mapping_keeps_identical_template_instances_separate() {
    let directory =
        std::env::temp_dir().join(format!("component-model-alias-{}", std::process::id()));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(
        &path,
        "template Child(){signal input in;signal output bit;bit<==in;}\
        template Parent(){component c=Child();c.in<==0;component d=Child();d.in<==1;}\
        component main=Parent();",
    )
    .unwrap();
    let project = lift_project(&load_sources(
        &[path],
        &[directory],
        VersionPolicy::new(Version::new(2, 2, 3)),
    ));
    let provider = ProjectSummaries::build(&project, Curve::Goldilocks).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &project.hir)
    else {
        panic!("main call")
    };
    let caller = provider.main_evidence(&call).unwrap();
    let parent = project.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&project.hir, parent).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
    let mut instances = Vec::new();
    for site in provider.graph().calls_from(CallOwner::Definition(parent)) {
        let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
        else {
            panic!("child call")
        };
        instances.push(provider.enumerate_call(&facts, &caller, &call, 1).unwrap());
    }
    let first = &instances[0];
    let cfg = build_cfg(&project.hir, first.callee.context().definition()).unwrap();
    let child = provider.analyze_for_evidence(&cfg, &first.callee, None).unwrap();
    let ready =
        crate::interprocedural::input_relation::ready_model_instance(&facts, first).unwrap();
    let ports = crate::interprocedural::component_models::ValidatedComponentPorts::new(
        &facts, &child, first, &ready,
    )
    .unwrap();
    let own = facts.applied_component_key(first.outputs[0].applied_port());
    let other = facts.applied_component_key(instances[1].outputs[0].applied_port());
    let own = own.certified().unwrap();
    let other = other.certified().unwrap();
    assert_ne!(own, other);
    assert!(ports.contains_output(own));
    assert!(ports.child_key(own).is_some());
    assert!(!ports.contains_output(other));
    assert!(ports.child_key(other).is_none());
}

#[test]
fn component_port_expansion_preserves_exact_boundaries_and_handle_order() {
    let cases = [
        ("", Err(SummaryBlocker::UnsupportedContext)),
        ("[2][3]", Err(SummaryBlocker::UnsupportedContext)),
        ("[0]", Err(SummaryBlocker::ContextBudget)),
        ("[1]", Ok(1)),
        ("[512]", Ok(512)),
        ("[513]", Err(SummaryBlocker::ContextBudget)),
        ("[n]", Err(SummaryBlocker::UnsupportedContext)),
    ];
    for (shape, expected) in cases {
        let project = crate::test_fixtures::port_project(shape);
        let provider = ProjectSummaries::build(&project, Curve::Goldilocks).unwrap();
        let definition = project.hir.definition("T").unwrap();
        let evidence = provider.symbolic_root(definition).unwrap();
        let cfg = build_cfg(&project.hir, definition).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let DefinitionRef::Template(template) = definition else { panic!("template T") };
        let ports = &project.hir.template(template).unwrap().ports;

        let result =
            checked_bit_port_handles(&facts, ports[0], ports[1]).map(|(_, handles)| handles);
        match expected {
            Ok(width) => {
                let handles = result.unwrap();
                assert_eq!(handles.len(), width);
                for (index, handle) in handles.iter().enumerate() {
                    assert_eq!(handle, &facts.port_handle(ports[1], &[index]).unwrap());
                }
            }
            Err(blocker) => assert_eq!(result.unwrap_err(), blocker, "{shape}"),
        }
    }
}
