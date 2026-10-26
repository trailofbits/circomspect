//! Trace local arithmetic from a library root through certified facts to a warning or abstention.
// These executable contracts intentionally panic when a characterized result changes.
// Rust 1.74 requires `allow` because `expect` lint attributes are not yet stable.
#![allow(clippy::allow_attributes, clippy::panic_in_result_fn)]

mod support;

use std::collections::BTreeSet;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::{FactBlocker, FieldContext, Range};
use circomspect_program_analysis::interprocedural::ProjectAnalysis;
use circomspect_program_analysis::rules::{
    run_registered, AbstentionReason, RuleContext, RuleKind, SourceMap,
};
use parser::frontend::BinaryOperator;
use parser::hir::{lift_project, ExprKind};
use program_structure::constants::Curve;

use crate::support::{loaded, ExampleResult};

#[derive(Clone, Copy)]
enum Operand {
    Exact,
    Symbolic,
}

fn check(source: &str, operand: Operand) -> ExampleResult {
    let loaded = loaded(source);
    let project = lift_project(&loaded);
    let definition = project.hir.definition("T").ok_or("missing template T")?;
    let analysis = ProjectAnalysis::build(&project, Curve::Goldilocks)
        .map_err(|error| format!("call graph: {error:?}"))?;
    let evidence =
        analysis.symbolic_root(definition).map_err(|error| format!("root: {error:?}"))?;
    let cfg = build_cfg(&project.hir, definition).map_err(|error| format!("CFG: {error:?}"))?;
    let facts = analysis
        .analyze_for_evidence(&cfg, &evidence, None)
        .map_err(|error| format!("local facts: {error:?}"))?;
    let expression = project
        .hir
        .expressions()
        .iter()
        .find(|expression| {
            if let ExprKind::Binary { operator: BinaryOperator::Subtract, left: _, right: _ } =
                expression.kind
            {
                return true;
            }
            false
        })
        .ok_or("missing subtraction")?;
    let ExprKind::Binary { operator: BinaryOperator::Subtract, left, right } = expression.kind
    else {
        return Err("expected subtraction".into());
    };
    let field = FieldContext::for_curve(Curve::Goldilocks);
    assert_eq!(facts.reachable_expression(expression.id).certified(), Some(&true));
    assert_eq!(facts.range(right).certified(), Some(&Range::Exact(field.canonical(1.into()))));
    let context = RuleContext::new(&facts, &analysis, &evidence)?;
    let result = run_registered(&context)?;
    let findings: Vec<_> = result
        .findings()
        .iter()
        .filter(|finding| finding.kind() == RuleKind::FieldArithmetic)
        .collect();
    let abstentions: Vec<_> = result
        .abstentions()
        .iter()
        .filter(|abstention| abstention.kind == RuleKind::FieldArithmetic)
        .collect();
    match operand {
        Operand::Exact => {
            assert_eq!(
                facts.range(left).certified(),
                Some(&Range::Exact(field.canonical(0.into())))
            );
            assert_eq!(findings.len(), 1);
            assert_eq!(abstentions.len(), 0, "unexpected abstentions: {abstentions:?}");
            let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id])?;
            let report = findings[0].to_report(&sources)?;
            assert_eq!(report.id(), "CS0004");
            assert_eq!(
                report.message(),
                concat!(
                    "Exact operands produce -1; field arithmetic reduces it to ",
                    "18446744069414584320 modulo the selected prime."
                )
            );
            assert_eq!(report.primary().len(), 1);
            assert_eq!(report.primary()[0].range, 39..42);
            assert_eq!(report.primary()[0].message, "Proved modular wraparound");
            assert_eq!(
                Some(report.primary()[0].file_id),
                sources.file_id(expression.span.source())
            );
        }
        Operand::Symbolic => {
            let blockers = BTreeSet::from([FactBlocker::DeferredShape(left)]);
            assert_eq!(facts.range(left).unavailable(), Some(&blockers));
            assert!(findings.is_empty());
            assert_eq!(abstentions.len(), 1);
            assert_eq!(abstentions[0].reason, AbstentionReason::LocalFacts(blockers));
            assert_eq!(abstentions[0].span, expression.span);
            assert_eq!((expression.span.start(), expression.span.end()), (40, 43));
        }
    }
    Ok(())
}

fn main() -> ExampleResult {
    check("template T(){signal output out;out <== 0-1;}", Operand::Exact)?;
    check("template T(x){signal output out;out <== x-1;}", Operand::Symbolic)
}

#[test]
fn reading_contract() -> ExampleResult {
    main()
}
