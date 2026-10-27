//! Follow exact main/child evidence through a checked comparator model and a rejected candidate.
// These executable contracts intentionally panic when a characterized result changes.
// Rust 1.74 requires `allow` because `expect` lint attributes are not yet stable.
#![allow(clippy::allow_attributes, clippy::panic_in_result_fn)]

mod support;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::interprocedural::{CallOwner, CallReachability, ProjectAnalysis};
use circomspect_program_analysis::rules::{run_registered, RuleContext, RuleKind, SourceMap};
use parser::hir::lift_project;
use program_structure::constants::Curve;

use crate::support::{loaded, ExampleResult};

// Keep source offsets visible: repeated loop equations share spans but have distinct occurrences.
const SOURCE: &str = concat!(
    "template Encoding(){signal input x;signal output y[3];var sum=0;",
    "for(var i=0;i<3;i++){y[i]<--(x>>i)&1;y[i]*(y[i]-1)===0;sum+=y[i]*(2**i);}",
    "x===sum;}template Comparison(){signal input x[2];signal output y;",
    "component e=Encoding();e.x<==x[0]+4-x[1];y<==1-e.y[2];}",
    "template Main(){signal output y;component c=Comparison();",
    "c.x[0]<==4;c.x[1]<==1;y<==c.y;}component main=Main();"
);

#[derive(Clone, Copy)]
enum Expected {
    RangeViolation,
    NoViolation,
}

fn check(source: &str, expected: Expected) -> ExampleResult {
    let loaded = loaded(source);
    let project = lift_project(&loaded);
    let analysis = ProjectAnalysis::build(&project, Curve::Goldilocks)
        .map_err(|error| format!("call graph: {error:?}"))?;
    let site = analysis.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        analysis.graph().reachable_main_call(site.id(), &project.hir)
    else {
        return Err("main must be reachable".into());
    };
    let evidence =
        analysis.contexts().main_evidence(&call).map_err(|error| format!("main: {error:?}"))?;
    let cfg = build_cfg(&project.hir, evidence.context().definition())
        .map_err(|error| format!("CFG: {error:?}"))?;
    let facts = analysis
        .contexts()
        .analyze_for_evidence(&cfg, &evidence, None)
        .map_err(|error| format!("local facts: {error:?}"))?;
    let outputs = analysis.components().exact_component_outputs(&facts, &evidence);
    let outputs = outputs.certified().ok_or("component outputs unavailable")?;
    assert_eq!(outputs.len(), 1);
    let applied = outputs[0].applied_port();
    let proof = analysis.components().component_comparator_range(&facts, applied);
    let violations = proof.certified().ok_or("comparator query unavailable")?;
    let context = RuleContext::new(&facts, &analysis, &evidence)?;
    let result = run_registered(&context)?;
    let findings: Vec<_> = result
        .findings()
        .iter()
        .filter(|finding| finding.kind() == RuleKind::UnconstrainedLessThan)
        .collect();
    assert!(!result
        .abstentions()
        .iter()
        .any(|abstention| abstention.kind == RuleKind::UnconstrainedLessThan));
    match expected {
        Expected::RangeViolation => {
            assert_eq!(violations.len(), 1);
            let violation = &violations[0];
            assert_eq!(violation.applied_port(), applied);
            assert_eq!(violation.value().as_bigint().to_string(), "4");
            assert_eq!(violation.upper_bound().to_string(), "4");
            let origins: Vec<_> = violation
                .constraint_origins()
                .iter()
                .map(|origin| (origin.span.start(), origin.span.end()))
                .collect();
            assert_eq!(
                origins,
                vec![
                    (314, 324),
                    (325, 335),
                    (336, 343),
                    (225, 242),
                    (243, 255),
                    (101, 119),
                    (101, 119),
                    (101, 119),
                    (137, 145),
                ]
            );
            assert_eq!(findings.len(), 1);
            let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id])?;
            assert_eq!(findings[0].to_report(&sources)?.id(), "CS0014");
        }
        Expected::NoViolation => {
            // This query certifies an empty result. It does not prove safe inputs, uniqueness,
            // or unsatisfiability.
            assert_eq!(violations.as_slice(), []);
            assert!(findings.is_empty());
        }
    }
    Ok(())
}

fn main() -> ExampleResult {
    check(SOURCE, Expected::RangeViolation)?;
    check(&SOURCE.replace("y<==c.y;", "y<==c.y;y===1;"), Expected::NoViolation)
}

#[test]
fn reading_contract() -> ExampleResult {
    main()
}
