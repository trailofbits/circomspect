// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use std::fs;
use abstract_interpretation::graph::NodeId;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::{AccessHandle, AnalysisFacts, FactBlocker};
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ContextEvidence, ProjectAnalysis, SummaryBlocker, SummaryFact,
};
use parser::hir::{lift_project, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-component-port-bounds-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let file = directory.join("case.circom");
    fs::write(&file, source).unwrap();
    let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

fn main_evidence(provider: &ProjectAnalysis<'_>, project: &LiftedProject) -> ContextEvidence {
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &project.hir)
    else {
        panic!("main must resolve")
    };
    provider.contexts().main_evidence(&call).unwrap()
}

fn with_parent<T>(
    project: &LiftedProject,
    curve: Curve,
    work: impl FnOnce(&ProjectAnalysis<'_>, &AnalysisFacts<'_>, &ContextEvidence) -> T,
) -> T {
    let provider = ProjectAnalysis::build(project, curve).unwrap();
    let caller = main_evidence(&provider, project);
    let definition = project.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &caller, None).unwrap();
    work(&provider, &facts, &caller)
}

fn local_handle(
    project: &LiftedProject,
    curve: Curve,
    call_index: usize,
    port_name: &str,
    indices: &[usize],
) -> AccessHandle {
    with_parent(project, curve, |provider, facts, caller| {
        let site =
            provider.graph().calls_from(CallOwner::Definition(facts.definition()))[call_index];
        let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), facts)
        else {
            if let CallReachability::Unavailable(blocker) =
                provider.graph().reachable_call(site.id(), facts)
            {
                panic!("child call unavailable: {blocker:?}");
            }
            panic!("child call unreachable");
        };
        let child = provider.contexts().call_evidence(&call, facts, caller).unwrap();
        let cfg = build_cfg(&project.hir, call.callee()).unwrap();
        let child_facts = provider.contexts().analyze_for_evidence(&cfg, &child, None).unwrap();
        let port = project
            .hir
            .ports()
            .iter()
            .find(|port| project.hir.symbol(port.symbol).unwrap().name == port_name)
            .unwrap();
        child_facts.port_handle(port.id, indices).unwrap()
    })
}

const TWO_INSTANCES: &str = concat!(
    "template Child(n){signal input in;signal output bits[n];",
    "bits[0]<==0;if(n>1){bits[1]<==1;}}",
    "template Parent(){component c[2];c[0]=Child(1);c[1]=Child(2);",
    "c[0].in<==0;c[1].in<==0;}component main=Parent();"
);

#[test]
fn exact_child_parameter_checks_output_port_dimensions() {
    for dimension in ["2", "n", "n+0"] {
        let source = format!(
            "template Child(n){{signal output bits[{dimension}];bits[0]<==0;bits[1]<==1;}}\
             template Parent(){{component c=Child(2);}}component main=Parent();"
        );
        let project = fixture(&source);
        let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
        let main = main_evidence(&provider, &project);
        let definition = project.hir.definition("Parent").unwrap();
        let cfg = build_cfg(&project.hir, definition).unwrap();
        let facts = provider.contexts().analyze_for_evidence(&cfg, &main, None).unwrap();
        let outputs = provider.components().exact_component_outputs(&facts, &main);
        assert_eq!(outputs.certified().map(Vec::len), Some(2), "{dimension}: {outputs:?}");
    }
}

#[test]
fn provider_binds_a_parameter_checked_local_output_to_its_exact_call() {
    let project = fixture(concat!(
        "template Child(n){signal output bits[n];bits[0]<==0;bits[1]<==1;}",
        "template Parent(){component c=Child(2);}component main=Parent();"
    ));
    let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let caller = main_evidence(&provider, &project);
    let definition = project.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("child call must be reachable");
    };
    let child = provider.contexts().call_evidence(&call, &facts, &caller).unwrap();
    let cfg = build_cfg(&project.hir, call.callee()).unwrap();
    let child_facts = provider.contexts().analyze_for_evidence(&cfg, &child, None).unwrap();
    let output = project
        .hir
        .ports()
        .iter()
        .find(|port| project.hir.symbol(port.symbol).unwrap().name == "bits")
        .unwrap();
    let local = child_facts.port_handle(output.id, &[1]).unwrap();
    let result = provider.components().apply_component_local_output(&facts, &caller, &call, &local);
    let applied = result.certified().unwrap_or_else(|| panic!("{result:?}"));
    assert_eq!(applied.caller_evidence(), &caller);
    assert_eq!(applied.callee_evidence(), &child);
    assert_eq!(applied.port_summary().indices(), [1]);
    assert!(child_facts.port_handle(output.id, &[2]).is_err());
}

#[test]
fn differing_parameter_instances_keep_contexts_and_port_bounds_separate() {
    let project = fixture(TWO_INSTANCES);
    let short = local_handle(&project, Curve::Bn254, 0, "bits", &[0]);
    let long = local_handle(&project, Curve::Bn254, 1, "bits", &[0]);
    with_parent(&project, Curve::Bn254, |provider, facts, caller| {
        let sites = provider.graph().calls_from(CallOwner::Definition(facts.definition()));
        for (index, local) in [short, long].iter().enumerate() {
            for (site_index, site) in sites.iter().enumerate() {
                let CallReachability::Reachable(call) =
                    provider.graph().reachable_call(site.id(), facts)
                else {
                    panic!("child must be reachable")
                };
                let applied =
                    provider.components().apply_component_local_output(facts, caller, &call, local);
                assert_eq!(applied.certified().is_some(), index == site_index, "{applied:?}");
            }
        }
        let outputs = provider.components().exact_component_outputs(facts, caller);
        let outputs = outputs.certified().unwrap_or_else(|| panic!("{outputs:?}"));
        assert_eq!(outputs.len(), 3);
        assert_eq!(outputs[0].applied_port().port_summary().indices(), [0]);
        assert_eq!(outputs[2].applied_port().port_summary().indices(), [1]);
        assert_ne!(
            outputs[0].applied_port().callee_evidence(),
            outputs[2].applied_port().callee_evidence()
        );
        assert_ne!(outputs[0].applied_port().handle(), outputs[2].applied_port().handle());
    });
}

#[test]
fn foreign_curve_project_and_input_handles_cannot_be_applied() {
    let project = fixture(TWO_INSTANCES);
    let foreign = fixture(TWO_INSTANCES);
    let handles = [
        local_handle(&project, Curve::Goldilocks, 0, "bits", &[0]),
        local_handle(&foreign, Curve::Bn254, 0, "bits", &[0]),
        local_handle(&project, Curve::Bn254, 0, "in", &[]),
    ];
    with_parent(&project, Curve::Bn254, |provider, facts, caller| {
        let site = provider.graph().calls_from(CallOwner::Definition(facts.definition()))[0];
        let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), facts)
        else {
            panic!("child must be reachable")
        };
        for handle in handles {
            let result =
                provider.components().apply_component_local_output(facts, caller, &call, &handle);
            assert!(result.unavailable().is_some(), "{result:?}");
        }
    });
}

#[test]
fn wrong_caller_and_incomplete_caller_cannot_borrow_a_valid_local_handle() {
    let project = fixture(TWO_INSTANCES);
    let local = local_handle(&project, Curve::Bn254, 0, "bits", &[0]);
    with_parent(&project, Curve::Bn254, |provider, facts, caller| {
        let site = provider.graph().calls_from(CallOwner::Definition(facts.definition()))[0];
        let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), facts)
        else {
            panic!("child must be reachable")
        };
        let wrong = provider.contexts().symbolic_root(facts.definition()).unwrap();
        let result =
            provider.components().apply_component_local_output(facts, &wrong, &call, &local);
        assert_blocked(&result, SummaryBlocker::WrongContext);
        let warm = provider.components().apply_component_local_output(facts, caller, &call, &local);
        let applied = warm.certified().unwrap_or_else(|| panic!("{warm:?}"));
        let port = applied.port_summary().port();
        assert_eq!(
            provider.components().apply_component_output(facts, caller, &call, applied.handle()),
            warm,
        );
        assert_eq!(
            provider.components().apply_component_first_output(facts, caller, &call, port),
            warm
        );
        let cfg = build_cfg(&project.hir, facts.definition()).unwrap();
        for (limit, pending_node) in [(0, 0), (1, 0), (4, 2)] {
            let pending =
                provider.contexts().analyze_for_evidence(&cfg, caller, Some(limit)).unwrap();
            let result =
                provider.components().apply_component_local_output(&pending, caller, &call, &local);
            let blocker = SummaryBlocker::LocalFacts(std::collections::BTreeSet::from([
                FactBlocker::Budget(NodeId::new(pending_node)),
            ]));
            assert_blocked(&result, blocker.clone());
            assert_blocked(
                &provider.components().apply_component_first_output(&pending, caller, &call, port),
                blocker,
            );
            assert_blocked(
                &provider.components().apply_component_output(
                    &pending,
                    caller,
                    &call,
                    applied.handle(),
                ),
                SummaryBlocker::ExternalSummary,
            );
        }
    });
}

#[test]
fn source_instance_bounds_and_child_failures_still_block_enumeration() {
    for source in [
        concat!(
            "template Child(n){signal output out[n];out[0]<==1;}",
            "template Parent(){component c[1];c[1]=Child(1);}component main=Parent();"
        ),
        concat!(
            "template Child(n){signal output out[n];out[0]<==1;}",
            "template Parent(){signal input i;component c[1];c[i]=Child(1);}",
            "component main=Parent();"
        ),
        concat!(
            "template Child(n){signal output out[n];out[0]<==1;assert(0);}",
            "template Parent(){component c=Child(1);}component main=Parent();"
        ),
        concat!(
            "template Child(n){signal output out[n];out[0]<==1;}",
            "template Parent(){signal input n;component c=Child(n);}component main=Parent();"
        ),
    ] {
        let project = fixture(source);
        with_parent(&project, Curve::Bn254, |provider, facts, caller| {
            let result = provider.components().exact_component_outputs(facts, caller);
            assert!(result.unavailable().is_some(), "{source}: {result:?}");
        });
    }
}

#[test]
fn parameterized_multidimensional_ports_keep_all_checked_indices() {
    let project = fixture(concat!(
        "template Child(n){signal output bits[n][2];",
        "bits[0][0]<==0;bits[0][1]<==1;bits[1][0]<==2;bits[1][1]<==3;}",
        "template Parent(){component c=Child(2);}component main=Parent();"
    ));
    with_parent(&project, Curve::Bn254, |provider, facts, caller| {
        let outputs = provider.components().exact_component_outputs(facts, caller);
        let outputs = outputs.certified().unwrap_or_else(|| panic!("{outputs:?}"));
        let indices: Vec<_> =
            outputs.iter().map(|output| output.applied_port().port_summary().indices()).collect();
        assert_eq!(indices, [&[0, 0][..], &[0, 1], &[1, 0], &[1, 1]]);
    });
}

#[test]
fn a_function_call_cannot_apply_a_template_output_handle() {
    let project = fixture(concat!(
        "function F(){return 1;}template Child(){signal output bits;bits<==1;}",
        "template Parent(){component c=Child();log(F());}component main=Parent();"
    ));
    let local = local_handle(&project, Curve::Bn254, 0, "bits", &[]);
    with_parent(&project, Curve::Bn254, |provider, facts, caller| {
        let sites = provider.graph().calls_from(CallOwner::Definition(facts.definition()));
        for (index, site) in sites.iter().enumerate() {
            let CallReachability::Reachable(call) =
                provider.graph().reachable_call(site.id(), facts)
            else {
                panic!("call must be reachable")
            };
            let result =
                provider.components().apply_component_local_output(facts, caller, &call, &local);
            assert_eq!(result.certified().is_some(), index == 0, "{result:?}");
        }
    });
}

#[test]
fn same_parameter_instances_stay_distinct_and_late_bad_shapes_withhold_all_outputs() {
    for (second_size, complete) in [(1, true), (0, false)] {
        let source = format!(
            "template Child(n){{signal output bits[n];bits[0]<==1;}}\
             template Parent(n){{component c[n];c[0]=Child(1);c[1]=Child({second_size});}}\
             component main=Parent(2);"
        );
        let project = fixture(&source);
        with_parent(&project, Curve::Bn254, |provider, facts, caller| {
            let outputs = provider.components().exact_component_outputs(facts, caller);
            if complete {
                let outputs = outputs.certified().unwrap_or_else(|| panic!("{outputs:?}"));
                assert_eq!(outputs.len(), 2);
                assert_eq!(
                    outputs[0].applied_port().callee_evidence().context(),
                    outputs[1].applied_port().callee_evidence().context()
                );
                assert_ne!(outputs[0].applied_port().handle(), outputs[1].applied_port().handle());
            } else {
                assert!(outputs.unavailable().is_some(), "{outputs:?}");
            }
        });
    }
}

fn assert_blocked<T: std::fmt::Debug>(result: &SummaryFact<T>, blocker: SummaryBlocker) {
    assert_eq!(result.unavailable(), Some(&std::collections::BTreeSet::from([blocker])));
}

#[test]
fn component_instantiation_in_a_loop_remains_unavailable() {
    let project = fixture(concat!(
        "template Child(){signal output bits[1];bits[0]<==1;}",
        "template Parent(n){component c[n];for(var i=0;i<n;i++){c[i]=Child();}}",
        "component main=Parent(2);"
    ));
    with_parent(&project, Curve::Bn254, |provider, facts, caller| {
        let result = provider.components().exact_component_outputs(facts, caller);
        assert_blocked(
            &result,
            SummaryBlocker::LocalFacts(std::collections::BTreeSet::from([
                FactBlocker::OpaqueNode(NodeId::new(15), "unknown update value".into()),
                FactBlocker::DeferredControl(NodeId::new(11)),
            ])),
        );
    });
}

#[test]
fn competing_assignments_keep_selected_instance_refusals_on_every_entry() {
    for (assignment, blocker) in [
        ("c[0]=Child();", SummaryBlocker::DuplicateInstance),
        ("c[i]=Child();", SummaryBlocker::SymbolicInstance),
    ] {
        let source = format!(
            "template Child(){{signal output bits[1];bits[0]<==1;}}\
             template Parent(){{signal input i;component c[2];c[0]=Child();{assignment}}}\
             component main=Parent();"
        );
        let project = fixture(&source);
        let local = local_handle(&project, Curve::Bn254, 0, "bits", &[0]);
        with_parent(&project, Curve::Bn254, |provider, facts, caller| {
            let site = provider.graph().calls_from(CallOwner::Definition(facts.definition()))[0];
            let CallReachability::Reachable(call) =
                provider.graph().reachable_call(site.id(), facts)
            else {
                panic!("first call must be reachable")
            };
            let output = project.hir.ports()[0].id;
            let handle = facts
                .component_output_handle(project.hir.components()[0].id, &[0], output, &[0])
                .unwrap();
            for result in [
                provider.components().apply_component_output(facts, caller, &call, &handle),
                provider.components().apply_component_local_output(facts, caller, &call, &local),
                provider.components().apply_component_first_output(facts, caller, &call, output),
            ] {
                assert_blocked(&result, blocker.clone());
            }
            assert_blocked(
                &provider.components().exact_component_outputs(facts, caller),
                blocker.clone(),
            );
        });
    }
}

#[test]
fn local_context_checks_precede_competing_selected_assignments() {
    let source = concat!(
        "template Child(){signal output bits[1];bits[0]<==1;}",
        "template Parent(){component c;c=Child();c=Child();}component main=Parent();"
    );
    let project = fixture(source);
    let foreign = fixture(source);
    let handles = [
        local_handle(&project, Curve::Goldilocks, 0, "bits", &[0]),
        local_handle(&foreign, Curve::Bn254, 0, "bits", &[0]),
        local_handle(&project, Curve::Bn254, 1, "bits", &[0]),
    ];
    with_parent(&project, Curve::Bn254, |provider, facts, caller| {
        let site = provider.graph().calls_from(CallOwner::Definition(facts.definition()))[0];
        let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), facts)
        else {
            panic!("first child call must be reachable")
        };
        for (handle, blocker) in handles.iter().zip([
            SummaryBlocker::WrongContext,
            SummaryBlocker::WrongContext,
            SummaryBlocker::DuplicateInstance,
        ]) {
            assert_blocked(
                &provider.components().apply_component_local_output(facts, caller, &call, handle),
                blocker,
            );
            assert_blocked(
                &provider.components().apply_component_output(facts, caller, &call, handle),
                SummaryBlocker::WrongContext,
            );
        }
        let wrong = provider.contexts().symbolic_root(facts.definition()).unwrap();
        assert_blocked(
            &provider.components().apply_component_first_output(
                facts,
                &wrong,
                &call,
                project.hir.ports()[0].id,
            ),
            SummaryBlocker::WrongContext,
        );
    });
}
