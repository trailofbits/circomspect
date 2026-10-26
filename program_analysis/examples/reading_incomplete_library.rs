//! Recover a valid neighboring library definition while reporting syntax and missing-call errors.
// These executable contracts intentionally panic when a characterized result changes.
// Rust 1.74 requires `allow` because `expect` lint attributes are not yet stable.
#![allow(clippy::allow_attributes, clippy::panic_in_result_fn)]

mod support;

use std::fs;
use std::ops::Range as SourceRange;

use circomspect_program_analysis::application::{analyze_files, AnalysisOutput};
use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::{FieldContext, Range};
use circomspect_program_analysis::interprocedural::ProjectAnalysis;
use parser::frontend::BinaryOperator;
use parser::hir::{lift_project, ExprKind};
use program_structure::constants::Curve;

use crate::support::{loaded, ExampleResult};

const SOURCE: &str = concat!(
    "template Broken(){var value=;}",
    "function MissingCaller(){return Missing();}",
    "template Neighbor(){signal output out;out <== 0-1;}"
);
const SYNTAX: &str = "invalid statement; parsing continued at the next statement or block boundary";
const INCOMPLETE: &str = "Analysis is incomplete for this source scope.";

fn analyze(source: &str) -> Result<AnalysisOutput, Box<dyn std::error::Error>> {
    let nonce = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)?.as_nanos();
    let directory =
        std::env::temp_dir().join(format!("circomspect-reading-{}-{nonce}", std::process::id()));
    fs::create_dir(&directory)?;
    let path = directory.join("library.circom");
    fs::write(&path, source)?;
    let output = analyze_files(std::slice::from_ref(&path), &[], Curve::Goldilocks);
    fs::remove_file(path)?;
    fs::remove_dir(directory)?;
    Ok(output?)
}

fn check_diagnostics(output: &AnalysisOutput, expected: &[(&str, &str, SourceRange<usize>)]) {
    assert_eq!(output.diagnostics.len(), expected.len());
    for (report, (id, message, range)) in output.diagnostics.iter().zip(expected) {
        assert_eq!(report.id(), *id);
        assert_eq!(report.message(), *message);
        assert_eq!(report.primary().len(), 1);
        assert_eq!(&report.primary()[0].range, range);
    }
}

fn check_neighbor(output: &AnalysisOutput) -> ExampleResult {
    let reports: Vec<_> = output.scopes.iter().flat_map(|scope| &scope.reports).collect();
    assert_eq!(reports.len(), 1);
    let report = reports[0];
    assert_eq!(report.id(), "CS0004");
    assert_eq!(
        report.message(),
        concat!(
            "Exact operands produce -1; field arithmetic reduces it to ",
            "18446744069414584320 modulo the selected prime."
        )
    );
    assert_eq!(report.primary().len(), 1);
    let label = &report.primary()[0];
    assert_eq!(label.range, 119..122);
    assert_eq!(label.message, "Proved modular wraparound");
    let file = output.files.to_storage().get(label.file_id)?;
    assert!(std::path::Path::new(file.name()).ends_with("library.circom"));
    assert_eq!(&file.source()[label.range.clone()], "0-1");
    Ok(())
}

fn check_neighbor_facts() -> ExampleResult {
    let loaded = loaded(SOURCE);
    let project = lift_project(&loaded);
    let definition = project.hir.definition("Neighbor").ok_or("missing Neighbor")?;
    let analysis = ProjectAnalysis::build(&project, Curve::Goldilocks)
        .map_err(|error| format!("call graph: {error:?}"))?;
    let evidence =
        analysis.symbolic_root(definition).map_err(|error| format!("root: {error:?}"))?;
    let cfg = build_cfg(&project.hir, definition).map_err(|error| format!("CFG: {error:?}"))?;
    let facts = analysis
        .analyze_for_evidence(&cfg, &evidence, None)
        .map_err(|error| format!("local facts: {error:?}"))?;
    let field = FieldContext::for_curve(Curve::Goldilocks);
    let mut checked = 0;
    for expression in project.hir.expressions() {
        let ExprKind::Binary { operator: BinaryOperator::Subtract, left, right } = expression.kind
        else {
            continue;
        };
        assert_eq!(facts.reachable_expression(expression.id).certified(), Some(&true));
        assert_eq!(facts.range(left).certified(), Some(&Range::Exact(field.canonical(0.into()))));
        assert_eq!(facts.range(right).certified(), Some(&Range::Exact(field.canonical(1.into()))));
        checked += 1;
    }
    assert_eq!(checked, 1);
    Ok(())
}

fn main() -> ExampleResult {
    let output = analyze(SOURCE)?;
    check_diagnostics(
        &output,
        &[
            ("P1000", SYNTAX, 18..29),
            ("CS0019", "unresolved Function call `Missing`", 62..69),
            ("CS0020", INCOMPLETE, 39..52),
            ("CS0020", INCOMPLETE, 9..15),
        ],
    );
    check_neighbor(&output)?;
    check_neighbor_facts()?;

    // Equal-length padding makes the independent control's Neighbor span comparable.
    let start = SOURCE.find("template Neighbor").ok_or("missing Neighbor marker")?;
    let complete = format!("{}{}", " ".repeat(start), &SOURCE[start..]);
    let output = analyze(&complete)?;
    check_diagnostics(
        &output,
        &[("P1004", "No compiler version is specified; analyzing as Circom 2.2.3.", 0..0)],
    );
    assert_eq!(output.diagnostics[0].primary()[0].message, "Add `pragma circom 2.2.3;`.");
    check_neighbor(&output)?;

    let output = analyze(&SOURCE.replace("0-1", "0-"))?;
    check_diagnostics(
        &output,
        &[
            ("P1000", SYNTAX, 18..29),
            ("P1000", SYNTAX, 111..122),
            ("CS0019", "unresolved Function call `Missing`", 62..69),
            ("CS0020", INCOMPLETE, 39..52),
            ("CS0020", INCOMPLETE, 9..15),
            ("CS0020", INCOMPLETE, 82..90),
        ],
    );
    assert!(output.scopes.iter().all(|scope| scope.reports.is_empty()));
    Ok(())
}

#[test]
fn reading_contract() -> ExampleResult {
    main()
}
