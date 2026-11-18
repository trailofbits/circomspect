use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;

use parser::hir::{lift_project, DefinitionRef, ExprKind, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::build_cfg_with_exact_calls;
use crate::hir_facts::{
    analyze_owned_with_scalar_calls, analyze_seeded, AnalysisError, AnalysisOptions, FieldContext,
    OwnedAnalysisOptions,
};
use crate::interprocedural::{ArgumentValue, ProjectAnalysis};
use crate::scalar_evidence::ScalarExpressionEvidence;

fn fixture() -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-owned-facts-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let file = directory.join("case.circom");
    fs::write(&file, "function Pure(){return 9;}template Check(n){signal output x;x<==n+Pure();}")
        .unwrap();
    let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

#[test]
fn borrowed_and_owned_facts_preserve_complete_and_pending_results() {
    let lifted = fixture();
    let hir = &lifted.hir;
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = hir.definition("Check").unwrap();
    let DefinitionRef::Template(template) = definition else { panic!("template") };
    let parameter = hir.template(template).unwrap().parameters[0];
    let field = FieldContext::for_curve(Curve::Bn254);
    let call = hir
        .expressions()
        .iter()
        .find_map(|expression| {
            if let ExprKind::Call { .. } = expression.kind {
                Some(expression.id)
            } else {
                None
            }
        })
        .unwrap();
    let mut snapshots = Vec::new();
    for initial in [1, 2] {
        let value = field.canonical(initial.into());
        let context = provider
            .contexts()
            .context_for(definition, vec![ArgumentValue::Scalar(value.clone())])
            .unwrap();
        let mut calls = ScalarExpressionEvidence::empty(hir, &context, Curve::Bn254);
        calls.insert_call(call, field.canonical(9.into()), BTreeSet::new());
        let values = BTreeMap::from([(parameter, value)]);
        let cfg = build_cfg_with_exact_calls(hir, definition, &calls, &values).unwrap();
        for budget in [Some(0), None] {
            let borrowed = analyze_seeded(
                hir,
                Cow::Borrowed(&cfg),
                &field,
                AnalysisOptions {
                    values: values.clone(),
                    calls: Some(Cow::Borrowed(&calls)),
                    budget,
                },
            )
            .unwrap();
            let owned = analyze_owned_with_scalar_calls(
                hir,
                cfg.clone(),
                &field,
                OwnedAnalysisOptions { values: values.clone(), calls: calls.clone(), budget },
            )
            .unwrap();
            assert_eq!(borrowed.forward, owned.forward);
            assert_eq!(borrowed.backward, owned.backward);
            assert_eq!(borrowed.demand, owned.demand);
            assert_eq!(borrowed.refined_context(), Some(&context));
            assert_eq!(owned.refined_context(), Some(&context));
            let ranges: Vec<_> = hir
                .expressions()
                .iter()
                .map(|expression| {
                    let expected = borrowed.range(expression.id);
                    assert_eq!(owned.range(expression.id), expected);
                    assert_eq!(owned.range(expression.id), expected);
                    expected
                })
                .collect();
            assert_eq!(borrowed.body_signal_reads_ready(), owned.body_signal_reads_ready());
            assert_eq!(
                borrowed.no_possible_repeated_body_writes(),
                owned.no_possible_repeated_body_writes()
            );
            assert_eq!(borrowed.generated_constraints_valid(), owned.generated_constraints_valid());
            if budget.is_none() {
                snapshots.push((owned, ranges));
            }
        }
    }
    assert_ne!(snapshots[0].1, snapshots[1].1);
    for (facts, ranges) in snapshots {
        for (expression, expected) in hir.expressions().iter().zip(ranges) {
            assert_eq!(facts.range(expression.id), expected);
        }
    }
}

#[test]
fn owned_analysis_rejects_project_then_calls_then_scalar_seeds() {
    let lifted = fixture();
    let other = fixture();
    let hir = &lifted.hir;
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = hir.definition("Check").unwrap();
    let DefinitionRef::Template(template) = definition else { panic!("template") };
    let field = FieldContext::for_curve(Curve::Bn254);
    let value = field.canonical(1.into());
    let context = provider
        .contexts()
        .context_for(definition, vec![ArgumentValue::Scalar(value.clone())])
        .unwrap();
    let calls = ScalarExpressionEvidence::empty(hir, &context, Curve::Bn254);
    let values = BTreeMap::from([(hir.template(template).unwrap().parameters[0], value)]);
    let cfg = build_cfg_with_exact_calls(hir, definition, &calls, &values).unwrap();
    let wrong_calls = ScalarExpressionEvidence::empty(hir, &context, Curve::Goldilocks);
    let options = |calls| OwnedAnalysisOptions { values: BTreeMap::new(), calls, budget: None };
    let foreign = analyze_owned_with_scalar_calls(
        &other.hir,
        cfg.clone(),
        &field,
        options(wrong_calls.clone()),
    );
    assert_eq!(foreign.err(), Some(AnalysisError::ForeignProject));
    let foreign_calls =
        analyze_owned_with_scalar_calls(hir, cfg.clone(), &field, options(wrong_calls));
    assert_eq!(foreign_calls.err(), Some(AnalysisError::ForeignCallResults));
    let wrong_seeds = analyze_owned_with_scalar_calls(hir, cfg, &field, options(calls));
    assert_eq!(wrong_seeds.err(), Some(AnalysisError::WrongScalarSeeds));
}
