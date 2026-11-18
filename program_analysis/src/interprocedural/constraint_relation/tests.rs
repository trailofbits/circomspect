use abstract_interpretation::graph::FlowGraph;
use parser::frontend::{parse_source, LoadedProject, SourceFile, SourceId, Version, VersionPolicy};
use parser::hir::lift_project;
use program_structure::utils::constants::Curve;

use crate::hir_cfg::{build_cfg, CfgNodeKind};
use crate::interprocedural::ProjectAnalysis;

#[test]
fn temporary_template_views_preserve_generated_equation_fact_borrows() {
    let source = "template T(){signal input a;signal output x;x<--a;x===a;}";
    let policy = VersionPolicy::new(Version::new(2, 2, 3));
    let id = SourceId::new(0);
    let project = lift_project(&LoadedProject {
        policy,
        diagnostics: Vec::new(),
        files: vec![SourceFile {
            id,
            path: "equation-query-views.circom".into(),
            text: source.into(),
            outcome: parse_source(id, source, policy),
        }],
    });
    let analysis = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    let definition = project.hir.definition("T").unwrap();
    let evidence = analysis.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = analysis.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let mut witness = None;
    for id in facts.cfg().nodes() {
        if let CfgNodeKind::Witness { .. } = &facts.cfg().node(*id).unwrap().kind {
            witness = Some(*id);
            break;
        }
    }
    let witness = witness.unwrap();
    let first = analysis.templates().template_generated_equations(&facts, &evidence);
    let second = {
        let queries = analysis.templates();
        queries.template_generated_equations(&facts, &evidence)
    };
    let first = first.for_witness(witness);
    let second = second.for_witness(witness);
    assert_eq!(first, second);
    let equation = first.certified().unwrap().as_ref().unwrap();
    assert_eq!(equation.context(), &evidence);
    assert_eq!(equation.constraint_origins().len(), 1);
}
