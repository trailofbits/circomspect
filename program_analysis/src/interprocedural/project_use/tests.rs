use parser::frontend::{parse_source, LoadedProject, SourceFile, SourceId, Version, VersionPolicy};
use parser::hir::lift_project;
use program_structure::utils::constants::Curve;

use crate::hir_cfg::build_cfg;
use crate::interprocedural::{CallOwner, CallReachability, ProjectAnalysis, ProjectOutputStatus};

#[test]
fn temporary_project_use_views_preserve_owned_instance_paths() {
    let source = "template Leaf(){signal output out;out<==1;}\
        template Parent(){component child=Leaf();}component main=Parent();";
    let policy = VersionPolicy::new(Version::new(2, 2, 3));
    let id = SourceId::new(0);
    let project = lift_project(&LoadedProject {
        policy,
        diagnostics: Vec::new(),
        files: vec![SourceFile {
            id,
            path: "project-use-views.circom".into(),
            text: source.into(),
            outcome: parse_source(id, source, policy),
        }],
    });
    let (first, second, main, child_site) = {
        let analysis = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
        let site = analysis.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            analysis.graph().reachable_main_call(site.id(), &project.hir)
        else {
            panic!("main call")
        };
        let main = analysis.contexts().main_evidence(&call).unwrap();
        let cfg = build_cfg(&project.hir, main.context().definition()).unwrap();
        let facts = analysis.contexts().analyze_for_evidence(&cfg, &main, None).unwrap();
        let child_site =
            analysis.graph().calls_from(CallOwner::Definition(facts.definition()))[0].id();
        let first = analysis.project_uses().closed_project_output_uses(&facts, &main);
        let second = {
            let queries = analysis.project_uses();
            queries.closed_project_output_uses(&facts, &main)
        };
        (first, second, main, child_site)
    };
    assert_eq!(first, second);
    let outputs = first.certified().unwrap();
    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0].main_evidence(), &main);
    assert_eq!(outputs[0].status(), ProjectOutputStatus::Unused);
    assert_eq!(outputs[0].instance_depth(), 1);
    assert_eq!(outputs[0].instance_path()[0].site(), child_site);
    assert!(outputs[0].instance_path()[0].indices().is_empty());
    assert_eq!(outputs[0].source_span().source(), id);
}
