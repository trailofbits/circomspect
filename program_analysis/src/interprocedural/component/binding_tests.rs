use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use parser::hir::{lift_project, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::component_fixture::repeat_constructor_source;
use crate::hir_cfg::{build_cfg, CfgNodeKind};
use crate::hir_facts::{analyze, AnalysisFacts, FieldContext};
use crate::interprocedural::{
    CallOwner, CallReachability, ContextEvidence, ProjectAnalysis, SummaryBlocker,
};

fn project() -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-repeated-constructor-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::create_dir_all(&directory).unwrap();
    let file = directory.join("case.circom");
    std::fs::write(
        &file,
        concat!(
            "template Child(){signal output bits[1];bits[0]<==1;}",
            "template Parent(){component c[2];c[0]=Child();c[1]=Child();}component main=Parent();"
        ),
    )
    .unwrap();
    let loaded = load_sources(
        std::slice::from_ref(&file),
        std::slice::from_ref(&directory),
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    std::fs::remove_file(file).unwrap();
    std::fs::remove_dir(directory).unwrap();
    lift_project(&loaded)
}

fn check_binding(
    provider: &ProjectAnalysis<'_>,
    facts: &AnalysisFacts<'_>,
    caller: &ContextEvidence,
    repeated: bool,
) {
    provider.contexts().check_facts_for_evidence(facts, caller).unwrap();
    let sites = provider.graph().calls_from(CallOwner::Definition(facts.definition()));
    let output = provider.hir().ports()[0].id;
    let component = provider.hir().components()[0].id;
    let mut instantiations = Vec::new();
    for id in facts.cfg().nodes() {
        if let CfgNodeKind::Instantiate { .. } = facts.cfg().node(*id).unwrap().kind {
            assert_eq!(facts.reachable_node(*id).certified(), Some(&true));
            instantiations.push(*id);
        }
    }
    assert_eq!(instantiations.len(), 2);
    for (index, instantiation) in instantiations.into_iter().enumerate() {
        let site = if repeated { sites[0] } else { sites[index] };
        let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), facts)
        else {
            panic!("constructor must be reachable")
        };
        let callee = provider.contexts().call_evidence(&call, facts, caller).unwrap();
        let handle = facts.component_output_handle(component, &[index], output, &[0]).unwrap();
        let direct = provider.components().apply_component_output(facts, caller, &call, &handle);
        let direct = direct.certified().unwrap_or_else(|| panic!("{direct:?}"));
        assert_eq!(direct.instantiation(), instantiation);
        assert_eq!(direct.handle(), &handle);
        assert_eq!(direct.caller_evidence(), caller);
        assert_eq!(direct.callee_evidence(), &callee);
        assert_eq!(direct.port_summary().port(), output);
        assert_eq!(direct.port_summary().indices(), [0]);
        provider
            .components()
            .with_component_port_facts(&callee, |child| {
                let local = child.port_handle(output, &[0]).unwrap();
                for applied in [
                    provider
                        .components()
                        .apply_component_local_output(facts, caller, &call, &local),
                    provider
                        .components()
                        .apply_component_first_output(facts, caller, &call, output),
                ] {
                    if repeated {
                        assert_eq!(
                            applied.unavailable(),
                            Some(&BTreeSet::from([SummaryBlocker::DuplicateInstance,]))
                        );
                    } else {
                        assert_eq!(applied.certified(), Some(direct));
                    }
                }
                Ok(())
            })
            .unwrap();
    }
    let outputs = provider.exact_component_outputs(facts, caller);
    if repeated {
        assert_eq!(
            outputs.unavailable(),
            Some(&BTreeSet::from([SummaryBlocker::DuplicateInstance]))
        );
    } else {
        assert_eq!(outputs.certified().unwrap().len(), 2);
    }
}

#[test]
fn repeated_source_and_selected_instance_uniqueness_are_distinct() {
    let project = project();
    let provider = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(site.id(), &project.hir)
    else {
        panic!("main must resolve")
    };
    let caller = provider.contexts().main_evidence(&main).unwrap();
    provider.contexts().check_evidence(&caller).unwrap();
    let cfg = build_cfg(&project.hir, caller.context().definition()).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &caller, None).unwrap();
    check_binding(&provider, &facts, &caller, false);
    let cfg = repeat_constructor_source(&cfg);
    let field = FieldContext::for_curve(Curve::Bn254);
    let mut facts = analyze(&project.hir, &cfg, &field, None).unwrap();
    facts.bind_evidence(caller.clone());
    check_binding(&provider, &facts, &caller, true);
}

#[test]
fn temporary_component_views_preserve_owned_ports_and_checked_contexts() {
    use crate::interprocedural::component::binding::CheckedCallContext;

    let project = project();
    let analysis = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let main = analysis.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        analysis.graph().reachable_main_call(main.id(), &project.hir)
    else {
        panic!("main call")
    };
    let caller = analysis.contexts().main_evidence(&main).unwrap();
    let cfg = build_cfg(&project.hir, caller.context().definition()).unwrap();
    let facts = analysis.contexts().analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = analysis.graph().calls_from(CallOwner::Definition(facts.definition()))[0];
    let CallReachability::Reachable(call) = analysis.graph().reachable_call(site.id(), &facts)
    else {
        panic!("child call")
    };
    let callee = analysis.contexts().call_evidence(&call, &facts, &caller).unwrap();
    let output = project.hir.ports()[0].id;
    let component = project.hir.components()[0].id;
    let handle = facts.component_output_handle(component, &[0], output, &[0]).unwrap();
    let direct = analysis.components().apply_component_output(&facts, &caller, &call, &handle);
    let checked =
        CheckedCallContext::new(analysis.components().analysis, &facts, &caller, &call).unwrap();
    let checked_inner = {
        let queries = analysis.components();
        CheckedCallContext::new(queries.analysis, &facts, &caller, &call).unwrap()
    };
    let local =
        checked.with_port_facts(|child| Ok(child.port_handle(output, &[0]).unwrap())).unwrap();
    let inner_local = checked_inner
        .with_port_facts(|child| Ok(child.port_handle(output, &[0]).unwrap()))
        .unwrap();
    let port = analysis
        .components()
        .with_component_port_facts(&callee, |child| Ok(child.port_handle(output, &[0]).unwrap()))
        .unwrap();
    let applied = {
        let queries = analysis.components();
        queries.apply_component_local_output(&facts, &caller, &call, &local)
    };
    let direct = direct.certified().unwrap();
    let applied = applied.certified().unwrap();
    assert_eq!(applied, direct);
    assert_eq!(applied.handle(), &handle);
    assert_eq!(applied.caller_evidence(), &caller);
    assert_eq!(applied.callee_evidence(), &callee);
    assert_eq!(checked.callee(), &callee);
    assert_eq!(checked_inner.callee(), &callee);
    assert_eq!(inner_local, local);
    assert_eq!(port, local);
}
