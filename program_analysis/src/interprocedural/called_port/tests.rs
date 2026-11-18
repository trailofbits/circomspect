use parser::frontend::{parse_source, LoadedProject, SourceFile, SourceId, Version, VersionPolicy};
use parser::hir::lift_project;
use program_structure::utils::constants::Curve;

use crate::hir_cfg::build_cfg;
use crate::hir_facts::Incidence;
use crate::interprocedural::{CallOwner, CallReachability, ProjectAnalysis};

#[test]
fn temporary_component_views_preserve_called_input_summary() {
    let source = "template Quotient(){signal input divisor;signal output result;\
        result<--1/divisor;}template Main(){signal input x;component child=Quotient();\
        child.divisor<--x;}component main=Main();";
    let policy = VersionPolicy::new(Version::new(2, 2, 3));
    let id = SourceId::new(0);
    let project = lift_project(&LoadedProject {
        policy,
        diagnostics: Vec::new(),
        files: vec![SourceFile {
            id,
            path: "called-input-views.circom".into(),
            text: source.into(),
            outcome: parse_source(id, source, policy),
        }],
    });
    let (first, second, public, context, port) = {
        let analysis = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
        let site = analysis.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            analysis.graph().reachable_main_call(site.id(), &project.hir)
        else {
            panic!("main call")
        };
        let parent = analysis.contexts().main_evidence(&call).unwrap();
        let cfg = build_cfg(&project.hir, parent.context().definition()).unwrap();
        let facts = analysis.contexts().analyze_for_evidence(&cfg, &parent, None).unwrap();
        let site = analysis.graph().calls_from(CallOwner::Definition(facts.definition()))[0];
        let CallReachability::Reachable(call) = analysis.graph().reachable_call(site.id(), &facts)
        else {
            panic!("child call")
        };
        let child = analysis.contexts().call_evidence(&call, &facts, &parent).unwrap();
        let cfg = build_cfg(&project.hir, call.callee()).unwrap();
        let facts = analysis.contexts().analyze_for_evidence(&cfg, &child, None).unwrap();
        let port = project.hir.ports()[0].id;
        let first = analysis.components().called_input_port(&facts, &child, port, &[]).unwrap();
        let second = {
            let queries = analysis.components();
            queries.called_input_port(&facts, &child, port, &[]).unwrap()
        };
        let public = analysis.templates().template_port_for_evidence(&facts, &child, port, &[]);
        (first, second, public, child.context().clone(), port)
    };
    assert_eq!(first, second);
    assert_eq!(public.certified(), Some(&first));
    assert_eq!(first.context(), &context);
    assert_eq!(first.port(), port);
    assert!(first.indices().is_empty());
    assert_eq!(first.incidence(), Incidence::Zero);
    assert_eq!(first.fixed_value(), None);
}

#[test]
fn generated_equation_on_a_constant_binding_target_is_refused() {
    use crate::hir_facts::ProofBudget;
    use crate::interprocedural::input_relation::{CheckedInputBinding, WitnessInputValue};

    let source = "template Child(){signal input divisor;signal output result;result<--divisor;}\
        template Main(){component child=Child();child.divisor<==7;}component main=Main();";
    let policy = VersionPolicy::new(Version::new(2, 2, 3));
    let id = SourceId::new(0);
    let project = lift_project(&LoadedProject {
        policy,
        diagnostics: Vec::new(),
        files: vec![SourceFile {
            id,
            path: "called-input-domain.circom".into(),
            text: source.into(),
            outcome: parse_source(id, source, policy),
        }],
    });
    let analysis = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let definition = project.hir.definition("Main").unwrap();
    let evidence = analysis.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = analysis.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let equations = facts.generated_equation_sites(&mut ProofBudget::default());
    let equations = equations.certified().unwrap();
    let target = equations.keys().iter().find(|key| key.instance.is_some()).unwrap().clone();
    let binding = CheckedInputBinding {
        target,
        value: WitnessInputValue::Constant(analysis.field_context().parse("7").unwrap()),
        origins: Vec::new(),
    };
    assert_eq!(
        analysis.components().check_witness_domain(&binding, equations),
        Err(crate::interprocedural::SummaryBlocker::UnsupportedContext)
    );
}
