use abstract_interpretation::graph::FlowGraph;

use parser::frontend::{parse_source, LoadedProject, SourceFile, SourceId, Version, VersionPolicy};
use parser::hir::{lift_project, ExprKind};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::{build_cfg, CfgNodeKind};
use crate::interprocedural::{CallOwner, CallReachability, ProjectAnalysis};

#[test]
fn temporary_component_views_preserve_model_source_borrows() {
    let source = "template Child(){signal output bit;bit<==0;}\
        template Parent(){component c=Child();signal output y;y<==c.bit;}\
        component main=Parent();";
    let policy = VersionPolicy::new(Version::new(2, 2, 3));
    let id = SourceId::new(0);
    let project = lift_project(&LoadedProject {
        policy,
        diagnostics: Vec::new(),
        files: vec![SourceFile {
            id,
            path: "model-source-views.circom".into(),
            text: source.into(),
            outcome: parse_source(id, source, policy),
        }],
    });
    let analysis = ProjectAnalysis::build(&project, Curve::Goldilocks).unwrap();
    let site = analysis.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        analysis.graph().reachable_main_call(site.id(), &project.hir)
    else {
        panic!("main call")
    };
    let caller = analysis.contexts().main_evidence(&call).unwrap();
    let cfg = build_cfg(&project.hir, caller.context().definition()).unwrap();
    let facts = analysis.contexts().analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = analysis.graph().calls_from(CallOwner::Definition(facts.definition()))[0];
    let CallReachability::Reachable(call) = analysis.graph().reachable_call(site.id(), &facts)
    else {
        panic!("child call")
    };
    let expected_call = call.site().id();
    let callee = analysis.contexts().call_evidence(&call, &facts, &caller).unwrap();
    let cfg = build_cfg(&project.hir, call.callee()).unwrap();
    let child = analysis.contexts().analyze_for_evidence(&cfg, &callee, None).unwrap();
    let local = child.port_handle(project.hir.ports()[0].id, &[]).unwrap();
    let applied =
        analysis.components().apply_component_local_output(&facts, &caller, &call, &local);
    let applied = applied.certified().unwrap();
    let mut output_read = None;
    for site in facts.cfg().nodes() {
        let CfgNodeKind::Evaluate(expression) = &facts.cfg().node(*site).unwrap().kind else {
            continue;
        };
        let ExprKind::Access(path) = &project.hir.expression(*expression).unwrap().kind else {
            continue;
        };
        if path.component_output {
            output_read = Some((*site, path.clone()));
            break;
        }
    }
    let (site, expected_path) = output_read.unwrap();
    let first = analysis.components().single_model_call(&facts, applied).unwrap();
    let second = {
        let queries = analysis.components();
        queries.single_model_call(&facts, applied).unwrap()
    };
    let first_path =
        analysis.components().live_model_output(&facts, applied, site).unwrap().unwrap();
    let second_path = {
        let queries = analysis.components();
        queries.live_model_output(&facts, applied, site).unwrap().unwrap()
    };
    assert_eq!(first.site().id(), expected_call);
    assert_eq!(second.site().id(), expected_call);
    assert_eq!(first_path, &expected_path);
    assert_eq!(second_path, &expected_path);
    assert_eq!(first_path.span.source(), id);
}
