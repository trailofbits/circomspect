use std::fs;

use parser::hir::lift_project;
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::build_cfg;
use crate::interprocedural::input_relation::{
    ready_enumerated_instance, ready_witness_instance, WitnessInputValue,
};
use crate::interprocedural::{CallOwner, CallReachability, ProjectSummaries, SummaryBlocker};

fn inspect(binding: &str, extra: &str) -> Result<Vec<WitnessInputValue>, SummaryBlocker> {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-witness-readiness-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(
        &path,
        format!(
            "template Child(){{signal input in;signal output out;out<--in;}}\
        template Parent(){{signal input x;component c=Child();{binding}{extra}}}\
        component main=Parent();"
        ),
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
        return Err(SummaryBlocker::ForeignCall);
    };
    let caller = provider.main_evidence(&call)?;
    let definition = project.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = provider
        .analyze_for_evidence(&cfg, &caller, None)
        .map_err(|_| SummaryBlocker::UnsupportedContext)?;
    let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        return Err(SummaryBlocker::ForeignCall);
    };
    let instance = provider.enumerate_call(&facts, &caller, &call, 4)?;
    let ready = ready_witness_instance(&facts, &caller, &instance)?;
    assert!(ready_enumerated_instance(&facts, &instance).is_err());
    let symbolic = provider.symbolic_root(definition).unwrap();
    assert!(ready_witness_instance(&facts, &symbolic, &instance).is_err());
    let mut other = instance.clone();
    other.indices.push(0);
    assert!(!ready.matches(&facts, &other));
    let partial = provider.analyze_for_evidence(&cfg, &caller, Some(0)).unwrap();
    assert!(!ready.matches(&partial, &instance));
    assert!(ready_witness_instance(&partial, &caller, &instance).is_err());
    let cfg = build_cfg(&project.hir, call.callee()).unwrap();
    let child = provider
        .analyze_for_evidence(&cfg, &instance.callee, None)
        .map_err(|_| SummaryBlocker::UnsupportedContext)?;
    let completed = provider.completed_project_template(&child, &instance.callee, &[])?;
    let completed = provider.completed_witness_child(&facts, &instance, completed, &ready)?;
    provider.completed_project_template(&facts, &caller, &[completed])?;
    let port = project
        .hir
        .ports()
        .iter()
        .find(|port| project.hir.symbol(port.symbol).unwrap().name == "in")
        .unwrap();
    let binding = ready.binding(port.id).unwrap();
    assert_eq!(binding.origins.len(), 1);
    assert!(binding.target.instance.is_some());
    Ok(vec![binding.value.clone()])
}

#[test]
fn witness_only_inputs_receive_readiness_without_generated_provenance() {
    let constant = inspect("c.in<--7;", "signal out;out<--c.out;").unwrap();
    let [WitnessInputValue::Constant(value)] = constant.as_slice() else {
        panic!("expected witness constant");
    };
    assert_eq!(value.as_bigint().to_string(), "7");
    let signal = inspect("c.in<--x;", "signal out;out<--c.out;").unwrap();
    let [WitnessInputValue::ParentSignal(key)] = signal.as_slice() else {
        panic!("expected parent signal");
    };
    assert!(key.instance.is_none());
}

#[test]
fn witness_readiness_preserves_missing_duplicate_generated_and_early_read_refusals() {
    for (binding, extra) in [
        ("", ""),
        ("c.in<==7;", ""),
        ("c.in<==x;", ""),
        ("c.in<--7;c.in<--7;", ""),
        ("signal out;out<--c.out;c.in<--7;", ""),
        ("signal y;c.in<--y;", ""),
        ("c.in<--Missing();", ""),
        ("c.in<--1/0;", ""),
        ("signal input values[2];c.in<--values[x];", ""),
        ("signal input values[2];c.in<--values[2];", ""),
        ("signal input values[2];c.in<--values;", ""),
        ("c.in<--7;", "assert(0);"),
        ("c.in<--7;", "var bad=1/0;"),
    ] {
        assert!(inspect(binding, extra).is_err(), "{binding}{extra}");
    }
}

#[test]
fn witness_readiness_accepts_exact_array_elements_and_scalar_calculation() {
    for binding in ["signal input values[2];c.in<--values[1];", "var v=3;c.in<--v+4;"] {
        assert!(inspect(binding, "signal out;out<--c.out;").is_ok(), "{binding}");
    }
}
