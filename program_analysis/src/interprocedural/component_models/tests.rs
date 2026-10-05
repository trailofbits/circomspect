use std::fs;

use parser::hir::{lift_project, DefinitionRef};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::build_cfg;
use crate::hir_facts::ProofBudget;
use crate::interprocedural::component_models::RequestedBits;
use crate::interprocedural::{CallOwner, CallReachability, ProjectSummaries};

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
