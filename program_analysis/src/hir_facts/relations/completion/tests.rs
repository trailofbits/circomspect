use std::collections::BTreeMap;
use std::fs;

use parser::hir::lift_project;
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::build_cfg;
use crate::hir_facts::{generated_models_satisfy, AnalysisFacts, ProofBudget};
use crate::interprocedural::ProjectAnalysis;

fn with_facts(source: &str, run: impl FnOnce(&AnalysisFacts<'_>)) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-completion-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let project = lift_project(&load_sources(
        &[path],
        &[directory],
        VersionPolicy::new(Version::new(2, 2, 3)),
    ));
    let provider = ProjectAnalysis::build(&project, Curve::Goldilocks).unwrap();
    let definition = project.hir.definition("T").unwrap();
    let evidence = provider.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    run(&facts);
}

#[test]
fn source_owned_assignment_order_completes_values_without_claiming_other_constraints() {
    with_facts(
        "template T(){signal input a;signal output z;signal b;b<==a+1;z<==b*2;z===0;}",
        |facts| {
            let mut budget = ProofBudget::default();
            let sites = facts.generated_equation_sites(&mut budget);
            let sites = sites.certified().unwrap();
            let plan = facts.generated_assignments(sites, &mut budget).unwrap();
            let mut model = BTreeMap::new();
            for key in sites.keys() {
                model.insert(key.clone(), facts.field.canonical(7.into()));
            }
            assert!(plan.complete(facts.field, &mut model, &mut budget).unwrap());
            for (key, value) in &model {
                let expected = match facts.hir.symbol(key.root).unwrap().name.as_str() {
                    "a" => 7,
                    "b" => 8,
                    "z" => 16,
                    name => panic!("unexpected {name}"),
                };
                assert_eq!(value, &facts.field.canonical(expected.into()));
            }
            assert!(!generated_models_satisfy(facts.field, sites, &[&model], &mut budget).unwrap());
        },
    );
}

#[test]
fn completion_charges_preparation_and_each_model_evaluation() {
    with_facts("template T(){signal input a;signal output b;b<==a+1;}", |facts| {
        let sites = facts.generated_equation_sites(&mut ProofBudget::default());
        let sites = sites.certified().unwrap();
        for mut budget in
            [ProofBudget::limited(4096, 4096, 0, 4096), ProofBudget::limited(4096, 4096, 4096, 0)]
        {
            assert!(facts.generated_assignments(sites, &mut budget).is_err());
        }
        let plan = facts.generated_assignments(sites, &mut ProofBudget::default()).unwrap();
        let mut model = sites
            .keys()
            .iter()
            .cloned()
            .map(|key| (key, facts.field.canonical(0.into())))
            .collect();
        assert!(plan
            .complete(facts.field, &mut model, &mut ProofBudget::limited(4096, 4096, 4096, 0))
            .is_err());
        assert!(plan.complete(facts.field, &mut model, &mut ProofBudget::default()).unwrap());
    });
}

#[test]
fn cyclic_and_repeated_generated_targets_never_create_a_completion_order() {
    for source in
        ["template T(){signal a;signal b;a<==b;b<==a;}", "template T(){signal a;a<==0;a<==1;}"]
    {
        with_facts(source, |facts| {
            let sites = facts.generated_equation_sites(&mut ProofBudget::default());
            if let Some(sites) = sites.certified() {
                assert!(facts.generated_assignments(sites, &mut ProofBudget::default()).is_err());
            } else {
                assert!(sites.unavailable().is_some());
            }
        });
    }
}

#[test]
fn completion_rejects_sites_from_another_source_context() {
    with_facts("template T(){signal a;a<==0;}", |first| {
        let sites = first.generated_equation_sites(&mut ProofBudget::default());
        let sites = sites.certified().unwrap();
        with_facts("template T(){signal a;a<==1;}", |second| {
            assert!(second.generated_assignments(sites, &mut ProofBudget::default()).is_err());
        });
    });
}
