use std::fs;

use abstract_interpretation::graph::FlowGraph;
use num_bigint::BigInt;
use parser::hir::{lift_project, AccessPath, AccessStep, ArrayIndex, HirProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::build_cfg;
use crate::hir_facts::relations::ambiguity::{
    generated_models_satisfy, validate_models, CandidateModel,
};
use crate::hir_facts::relations::complete::ProofBudget;
use crate::hir_facts::{AnalysisFacts, BitAmbiguityOutcome, FieldContext};
use crate::interprocedural::ProjectAnalysis;

fn path(hir: &HirProject, name: &str, index: Option<usize>) -> AccessPath {
    let symbol = hir.symbols().iter().find(|symbol| symbol.name == name).unwrap();
    let mut steps = Vec::new();
    if let Some(index) = index {
        steps.push(AccessStep::Index {
            index: ArrayIndex::Constant(index.to_string()),
            span: symbol.span,
        });
    }
    AccessPath {
        root: symbol.id,
        terminal: symbol.id,
        steps,
        component_input: false,
        component_output: false,
        span: symbol.span,
    }
}

fn with_facts(action: impl FnOnce(&AnalysisFacts<'_>, &AccessPath, &[AccessPath])) {
    let mut source = "template T(){signal input in;signal output bits[64];".to_owned();
    let mut sum = String::new();
    let mut weight = BigInt::from(1);
    for index in 0..64 {
        source.push_str(&format!("bits[{index}]<--0;bits[{index}]*(bits[{index}]-1)===0;"));
        if index != 0 {
            sum.push('+');
        }
        sum.push_str(&format!("{weight}*bits[{index}]"));
        weight *= 2;
    }
    source.push_str(&format!("in==={sum};}}"));
    let directory = std::env::temp_dir().join(format!(
        "circomspect-model-budget-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let source_path = directory.join("case.circom");
    fs::write(&source_path, source).unwrap();
    let loaded =
        load_sources(&[source_path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty());
    let provider = ProjectAnalysis::build(&lifted, Curve::Goldilocks).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let input = path(&lifted.hir, "in", None);
    let bits: Vec<_> = (0..64).map(|index| path(&lifted.hir, "bits", Some(index))).collect();
    action(&facts, &input, &bits);
}

#[test]
fn model_budget_covers_collection_control_seeds_and_both_complete_checks() {
    with_facts(|facts, input, bits| {
        let generated = facts.generated_equation_sites(&mut ProofBudget::default());
        let generated = generated.certified().unwrap();
        let terms: usize = generated.sites().iter().map(|site| site.equation().term_count()).sum();
        let control = facts.cfg().nodes().len() + facts.cfg().edges().len();
        let sufficient = control + 3 * terms;
        for operations in [0, control - 1, control + terms, sufficient - 1] {
            let result = facts.local_bit_ambiguity(
                input,
                bits,
                &mut ProofBudget::limited(4096, 262_144, 4096, operations),
            );
            assert!(result.unavailable().is_some(), "{operations}: {result:?}");
        }
        let result = facts.local_bit_ambiguity(
            input,
            bits,
            &mut ProofBudget::limited(4096, 262_144, 4096, sufficient),
        );
        let Some(BitAmbiguityOutcome::Proved(certificate)) = result.certified() else {
            panic!("exactly sufficient budget must prove the models: {result:?}");
        };
        assert_eq!(certificate.assignments()[0].len(), 65);
        let repeated = facts.local_bit_ambiguity(
            input,
            bits,
            &mut ProofBudget::limited(4096, 262_144, 4096, sufficient - 1),
        );
        assert!(repeated.unavailable().is_some(), "{repeated:?}");
    });
}

#[test]
fn partial_assignment_cannot_be_validated_even_after_another_pair_succeeded() {
    with_facts(|facts, input, bits| {
        let result = facts.local_bit_ambiguity(input, bits, &mut ProofBudget::default());
        let Some(BitAmbiguityOutcome::Proved(certificate)) = result.certified() else {
            panic!("complete models must be available: {result:?}");
        };
        let generated = facts.generated_equation_sites(&mut ProofBudget::default());
        let generated = generated.certified().unwrap();
        let [first, mut second] = certificate.assignments().clone();
        assert!(second.remove(certificate.decomposition().input()).is_some());
        let result = validate_models(
            facts.field,
            generated,
            [CandidateModel(first), CandidateModel(second)],
            &mut ProofBudget::default(),
        );
        assert!(result.is_err());
    });
}

#[test]
fn one_checked_model_requires_every_equation_and_a_complete_assignment() {
    with_facts(|facts, input, bits| {
        let result = facts.local_bit_ambiguity(input, bits, &mut ProofBudget::default());
        let Some(BitAmbiguityOutcome::Proved(certificate)) = result.certified() else {
            panic!("complete model pair required: {result:?}");
        };
        let generated = facts.generated_equation_sites(&mut ProofBudget::default());
        let generated = generated.certified().unwrap();
        let first = &certificate.assignments()[0];
        assert!(generated_models_satisfy(
            facts.field,
            generated,
            &[first],
            &mut ProofBudget::default()
        )
        .unwrap());

        let mut changed = first.clone();
        changed
            .insert(certificate.decomposition().bits()[0].clone(), facts.field.canonical(1.into()));
        assert!(!generated_models_satisfy(
            facts.field,
            generated,
            &[&changed],
            &mut ProofBudget::default(),
        )
        .unwrap());

        changed.remove(certificate.decomposition().input());
        assert!(generated_models_satisfy(
            facts.field,
            generated,
            &[&changed],
            &mut ProofBudget::default(),
        )
        .is_err());
        assert!(generated_models_satisfy(
            facts.field,
            generated,
            &[first],
            &mut ProofBudget::limited(4096, 262_144, 4096, 0),
        )
        .is_err());
        let foreign = FieldContext::for_curve(Curve::Bn254);
        assert!(generated_models_satisfy(
            &foreign,
            generated,
            &[first],
            &mut ProofBudget::default(),
        )
        .is_err());
    });
}
