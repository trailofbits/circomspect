use parser::hir::lift_project;
use parser::new_frontend::{parse_source, LoadedProject, SourceFile, SourceId, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::build_cfg;
use crate::hir_facts::AnalysisFacts;
use crate::interprocedural::output_enumeration::EnumeratedComponentInstance;
use crate::interprocedural::{CallOwner, CallReachability, ProjectSummaries, SummaryBlocker};

fn with_instance(
    source: &str,
    work: impl FnOnce(
        &ProjectSummaries<'_>,
        &AnalysisFacts<'_>,
        &AnalysisFacts<'_>,
        EnumeratedComponentInstance,
    ),
) {
    let policy = VersionPolicy::new(Version::new(2, 2, 3));
    let id = SourceId::new(0);
    let project = lift_project(&LoadedProject {
        policy,
        files: vec![SourceFile {
            id,
            path: "generated-context.circom".into(),
            text: source.into(),
            outcome: parse_source(id, source, policy),
        }],
        diagnostics: Vec::new(),
    });
    assert!(project.syntax_diagnostics.is_empty(), "{:?}", project.syntax_diagnostics);
    let provider = ProjectSummaries::build(&project, Curve::Goldilocks).unwrap();
    let definition = project.hir.definition("Parent").unwrap();
    let caller = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("first constructor must be reachable")
    };
    let instance = provider.enumerate_call(&facts, &caller, &call, 4).unwrap();
    provider
        .with_component_port_facts(&instance.callee.clone(), |child| {
            work(&provider, &facts, child, instance);
            Ok(())
        })
        .unwrap();
}

#[test]
fn generated_context_requires_an_output_before_checking_child_identity() {
    for output in ["", "signal output empty[0];"] {
        let source =
            format!("template Child(){{{output}}}template Parent(){{component c=Child();}}");
        with_instance(&source, |provider, facts, child, instance| {
            assert!(instance.outputs.is_empty());
            assert_eq!(
                provider.generated_input_context(facts, child, &instance),
                Err(SummaryBlocker::UnsupportedContext)
            );
            assert_eq!(
                provider.generated_input_context(facts, facts, &instance),
                Err(SummaryBlocker::UnsupportedContext)
            );
        });
    }
}

#[test]
fn generated_source_identity_precedes_unproved_component_bounds() {
    with_instance(
        concat!(
            "template Child(){signal output out;out<==1;}",
            "template Parent(n){component good=Child();component c[n];c[0]=Child();}"
        ),
        |provider, facts, _child, mut instance| {
            let caller = instance.outputs[0].applied_port().caller_evidence().clone();
            let site = provider.graph().calls_from(CallOwner::Definition(facts.definition()))[1];
            let CallReachability::Reachable(call) =
                provider.graph().reachable_call(site.id(), facts)
            else {
                panic!("second constructor must be reachable")
            };
            let callee = provider.call_evidence(&call, facts, &caller).unwrap();
            let (component, target, instantiation) =
                provider.instantiated_component(facts, call.site().expression).unwrap();
            assert!(facts.component_bounds(component).is_err());
            assert_eq!(facts.reachable_node(instantiation).certified(), Some(&true));
            instance.site = site.id();
            instance.callee = callee.clone();
            instance.component = component;
            instance.instantiation = instantiation;
            instance.indices = vec![0];
            provider
                .with_component_port_facts(&callee, |child| {
                    assert_ne!(instance.target, target);
                    assert_eq!(
                        provider.generated_input_context(facts, child, &instance),
                        Err(SummaryBlocker::WrongInstance)
                    );
                    instance.target = target;
                    assert_eq!(
                        provider.generated_input_context(facts, child, &instance),
                        Err(SummaryBlocker::UnsupportedContext)
                    );
                    Ok(())
                })
                .unwrap();
        },
    );
}

#[test]
fn generated_context_rechecks_the_current_analysis_after_success() {
    with_instance(
        concat!(
            "template Child(){signal output out;out<==1;}",
            "template Parent(){component c=Child();}"
        ),
        |provider, facts, child, instance| {
            let caller = instance.outputs[0].applied_port().caller_evidence();
            assert_eq!(
                provider.generated_input_context(facts, child, &instance),
                Ok(caller.clone())
            );
            let pending = provider.analyze_for_evidence(facts.cfg(), caller, Some(0)).unwrap();
            let blockers = pending.reachable_node(pending.cfg().exit()).into_result().unwrap_err();
            assert_eq!(
                provider.generated_input_context(&pending, child, &instance),
                Err(SummaryBlocker::LocalFacts(blockers))
            );
        },
    );
}
