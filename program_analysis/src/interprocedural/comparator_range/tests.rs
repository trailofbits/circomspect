use std::fs;

use parser::hir::{lift_project, Effect};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::{build_cfg, Origin};
use crate::hir_facts::{AnalysisFacts, ProofBudget};
use crate::interprocedural::{AppliedComponentPort, CallOwner, CallReachability, ProjectAnalysis};

const SOURCE: &str = "template Encoding(){signal input x;signal output y[3];var sum=0;\
    for(var i=0;i<3;i++){y[i]<--(x>>i)&1;y[i]*(y[i]-1)===0;sum+=y[i]*(2**i);}x===sum;}\
    template Comparison(){signal input x[2];signal output y;component e=Encoding();\
    e.x<==x[0]+4-x[1];y<==1-e.y[2];}\
    template Main(){signal output y;component c=Comparison();c.x[0]<==4;c.x[1]<==1;y<==c.y;}\
    component main=Main();";

fn with_query<T>(
    source: &str,
    work: impl FnOnce(
        &ProjectAnalysis<'_>,
        &ProjectAnalysis<'_>,
        &AnalysisFacts<'_>,
        &AppliedComponentPort,
    ) -> T,
) -> T {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-comparator-provider-{}-{:?}",
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
    assert!(project.syntax_diagnostics.is_empty(), "{:?}", project.syntax_diagnostics);
    let provider = ProjectAnalysis::build(&project, Curve::Goldilocks).unwrap();
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(main.id(), &project.hir)
    else {
        panic!("main");
    };
    let evidence = provider.contexts().main_evidence(&call).unwrap();
    let cfg = build_cfg(&project.hir, evidence.context().definition()).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let outputs = provider.components().exact_component_outputs(&facts, &evidence);
    let applied = outputs.certified().unwrap()[0].applied_port();
    let other = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    work(&provider, &other, &facts, applied)
}

#[test]
fn comparator_models_keep_scope_curve_project_and_budget_identity() {
    with_query(SOURCE, |provider, other, facts, applied| {
        let result = provider.component_comparator_range(facts, applied);
        let result = result.certified().unwrap();
        assert_eq!(result.len(), 1);
        assert_eq!(result[0].value().as_bigint().to_string(), "4");
        assert_eq!(result[0].upper_bound().to_string(), "4");
        assert_eq!(result[0].applied_port(), applied);
        assert!(!result[0].constraint_origins().is_empty());
        let symbolic = provider.contexts().symbolic_root(facts.definition()).unwrap();
        let symbolic =
            provider.contexts().analyze_for_evidence(facts.cfg(), &symbolic, None).unwrap();
        assert!(provider.component_comparator_range(&symbolic, applied).certified().is_none());
        assert!(other.component_comparator_range(facts, applied).certified().is_none());
        for limit in 0..64 {
            let mut budget = ProofBudget::limited(4096, 4096, 4096, limit);
            assert!(
                provider.comparator_range_result(facts, applied, &mut budget).is_err(),
                "budget {limit}"
            );
        }
        for mut budget in [
            ProofBudget::limited(0, 4096, 4096, 4096),
            ProofBudget::limited(4096, 0, 4096, 4096),
            ProofBudget::limited(4096, 4096, 0, 4096),
        ] {
            assert!(provider.comparator_range_result(facts, applied, &mut budget).is_err());
        }
        with_query(SOURCE, |foreign, _, _, _| {
            assert!(foreign.component_comparator_range(facts, applied).certified().is_none());
        });
    });
}

#[test]
fn additional_free_inputs_never_turn_defaults_into_fixed_range_evidence() {
    for (source, expected) in [
        (
            SOURCE.replace(
                "signal output y;component c=Comparison();c.x[0]<==4;",
                "signal input z;signal output y;component c=Comparison();c.x[0]<==z;",
            ),
            0,
        ),
        (
            SOURCE.replace(
                "signal output y;component c=Comparison();c.x[0]<==4;",
                "signal input z;signal output y;component c=Comparison();c.x[0]<==z+4;",
            ),
            0,
        ),
        (
            SOURCE.replace(
                "signal output y;component c=Comparison();c.x[0]<==4;",
                "signal input z;z===0;signal output y;component c=Comparison();c.x[0]<==z+4;",
            ),
            1,
        ),
        (
            SOURCE.replace(
                "signal output y;component c=Comparison();c.x[0]<==4;",
                "signal input z;z===4;signal output y;component c=Comparison();c.x[0]<==z;",
            ),
            1,
        ),
        (SOURCE.replace("y<==c.y;", "y<==c.y;signal input z;z===7;z*y===0;"), 1),
        (SOURCE.replace("y<==c.y;", "y<==c.y;signal input z;z===7;z*y===1;"), 0),
    ] {
        with_query(&source, |provider, _, facts, applied| {
            let result = provider.component_comparator_range(facts, applied);
            let values = result
                .certified()
                .unwrap_or_else(|| panic!("{source}: {:?}", result.unavailable()));
            assert_eq!(values.len(), expected, "{source}");
        });
    }
}

#[test]
fn unreachable_library_body_errors_do_not_hide_a_complete_comparator() {
    let source = SOURCE.replace(
        "component main=Main();",
        "template Incomplete(){var x=Missing();}component main=Main();",
    );
    with_query(&source, |provider, _, facts, applied| {
        let result = provider.component_comparator_range(facts, applied);
        assert_eq!(
            result.certified().unwrap_or_else(|| panic!("{:?}", result.unavailable())).len(),
            1
        );
    });
}

#[test]
fn array_outputs_are_refused_before_any_comparator_proof_work() {
    let source = SOURCE
        .replace("signal output y;component e=", "signal output y[2];component e=")
        .replace("y<==1-e.y[2];", "y[0]<==1-e.y[2];y[1]<==0;")
        .replace("y<==c.y;", "y<==c.y[0];");
    with_query(&source, |provider, other, facts, applied| {
        let mut budget = ProofBudget::limited(0, 0, 0, 0);
        assert_eq!(
            provider.comparator_range_result(facts, applied, &mut budget),
            Err(crate::interprocedural::SummaryBlocker::UnsupportedContext)
        );
        let symbolic = provider.contexts().symbolic_root(facts.definition()).unwrap();
        let symbolic =
            provider.contexts().analyze_for_evidence(facts.cfg(), &symbolic, None).unwrap();
        let result = provider.component_comparator_range(&symbolic, applied);
        assert!(result
            .unavailable()
            .unwrap()
            .contains(&crate::interprocedural::SummaryBlocker::WrongContext));
        let result = other.component_comparator_range(facts, applied);
        assert!(!result
            .unavailable()
            .unwrap()
            .contains(&crate::interprocedural::SummaryBlocker::UnsupportedContext));
        with_query(&source, |foreign, _, _, _| {
            let result = foreign.component_comparator_range(facts, applied);
            assert!(!result
                .unavailable()
                .unwrap()
                .contains(&crate::interprocedural::SummaryBlocker::UnsupportedContext));
        });
    });
}

#[test]
fn comparator_constraint_origins_keep_every_scope_in_order() {
    with_query(SOURCE, |provider, _, facts, applied| {
        let result = provider.component_comparator_range(facts, applied);
        let violations = result.certified().unwrap();
        assert_eq!(violations.len(), 1);
        let mut expected = Vec::new();
        for marker in [
            "c.x[0]<==4",
            "c.x[1]<==1",
            "y<==c.y",
            "e.x<==x[0]+4-x[1]",
            "y<==1-e.y[2]",
            "y[i]*(y[i]-1)===0;",
            "y[i]*(y[i]-1)===0;",
            "y[i]*(y[i]-1)===0;",
            "x===sum;",
        ] {
            let mut origins = Vec::new();
            for block in facts.hir().blocks() {
                for (effect_index, effect) in block.effects.iter().enumerate() {
                    let (expression, span) =
                        if let Effect::ConstraintAssignment { value, span, .. }
                        | Effect::OpaqueAssignment { value, span, .. } = effect
                        {
                            (*value, *span)
                        } else if let Effect::EqualityConstraint { left, span, .. }
                        | Effect::OpaqueEquality { left, span, .. } = effect
                        {
                            (*left, *span)
                        } else {
                            continue;
                        };
                    if &SOURCE[span.start()..span.end()] == marker {
                        origins.push(Origin {
                            block: block.id,
                            effect_index,
                            expression: Some(expression),
                            span,
                        });
                    }
                }
            }
            assert_eq!(origins.len(), 1, "{marker}");
            expected.push(origins[0]);
        }
        assert_eq!(violations[0].constraint_origins(), expected);
    });
}

#[test]
fn comparator_closure_preserves_budget_outcomes_and_remaining_allowance() {
    let cases = [
        ("complete", SOURCE.to_string()),
        ("near_pattern", SOURCE.replace("y<==1-e.y[2]", "y<==2-e.y[2]")),
        ("main_equation", SOURCE.replace("y<==c.y;", "y<==c.y;y===1;")),
        ("leaf_equation", SOURCE.replace("x===sum;", "x===sum;y[0]===1;")),
        (
            "free_input",
            SOURCE.replace(
                "signal output y;component c=Comparison();c.x[0]<==4;",
                "signal input z;signal output y;component c=Comparison();c.x[0]<==z;",
            ),
        ),
    ];
    let mut records = Vec::new();
    for (case, source) in cases {
        with_query(&source, |provider, _, facts, applied| {
            for limit in
                [0, 1, 63, 64, 127, 128, 255, 256, 443, 444, 445, 511, 512, 1023, 1024, 4096, 8192]
            {
                let mut budget = ProofBudget::limited(4096, 262_144, 4096, limit);
                let result = provider.comparator_range_result(facts, applied, &mut budget);
                let result = match result {
                    Ok(violations) => violation_contract(&violations),
                    Err(blocker) => format!("{blocker:?}"),
                };
                let mut remaining = 0;
                while budget.reserve_control_step() {
                    remaining += 1;
                }
                records.push(format!("{case} {limit} {remaining} {result}"));
            }
        });
    }
    let records = records.join("\n") + "\n";
    assert_eq!(records, include_str!("closure_contract.txt"));
}

fn violation_contract(
    violations: &[crate::interprocedural::comparator_range::ComparatorRangeViolation],
) -> String {
    let mut records = Vec::new();
    for violation in violations {
        let span = violation.binding_span();
        let mut origins = Vec::new();
        for origin in violation.constraint_origins() {
            origins.push(format!("{}..{}", origin.span.start(), origin.span.end()));
        }
        records.push(format!(
            "{}<{}@{}..{} [{}]",
            violation.value().as_bigint(),
            violation.upper_bound(),
            span.start(),
            span.end(),
            origins.join(","),
        ));
    }
    format!("Ok({})", records.join(";"))
}
