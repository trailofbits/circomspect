// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::format_push_string,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
mod support;

use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::FieldContext;
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ProjectAnalysis, SummaryBlocker,
};
use circomspect_program_analysis::rules::{
    run_registered, AbstentionReason, RuleContext, RuleKind, RuleResult, SourceMap,
};
use parser::hir::lift_project;
use parser::frontend::{load_sources, LoadedProject, Version, VersionPolicy};
use program_structure::report::MessageCategory;
use program_structure::utils::constants::Curve;
use serde_json::Value;

fn source(left: &str, right: &str, assignment: &str) -> String {
    format!(
        "template Decompose(n){{signal input value;signal output bits[n];var sum=0;\
        for(var i=0;i<n;i++){{bits[i]<--(value >> i)&1;\
        bits[i]*(bits[i]-1)===0;sum+=bits[i]*(2**i);}}value===sum;}}\
        template Compare(n){{signal input operands[2];signal output answer;\
        component d=Decompose(n+1);d.value<==operands[0]+(1<<n)-operands[1];\
        answer<==1-d.bits[n];}}\
        template Main(){{signal output out;component c=Compare(8);\
        c.operands[0]{assignment}{left};c.operands[1]<=={right};out<==c.answer;}}\
        component main=Main();"
    )
}

fn inspect(source: &str, curve: Curve, budget: Option<usize>) -> (LoadedProject, RuleResult) {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-comparator-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let project = lift_project(&loaded);
    assert!(project.syntax_diagnostics.is_empty(), "{:?}", project.syntax_diagnostics);
    let provider = ProjectAnalysis::build(&project, curve).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &project.hir)
    else {
        panic!("main")
    };
    let evidence = provider.contexts().main_evidence(&call).unwrap();
    let cfg = build_cfg(&project.hir, evidence.context().definition()).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, budget).unwrap();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    (loaded, run_registered(&context).unwrap())
}

fn count(result: &RuleResult) -> usize {
    result
        .findings()
        .iter()
        .filter(|finding| finding.kind() == RuleKind::UnconstrainedLessThan)
        .count()
}

#[test]
fn arbitrary_named_nested_comparator_reports_constraint_fixed_out_of_range_inputs() {
    for curve in [Curve::Bn254, Curve::Goldilocks, Curve::Bls12_381] {
        let field = FieldContext::for_curve(curve.clone());
        let value = field.canonical((-254).into()).as_bigint().to_string();
        let (loaded, result) = inspect(&source(&value, "1", "<=="), curve, None);
        assert_eq!(count(&result), 1, "{:?}", result.abstentions());
        let finding = result
            .findings()
            .iter()
            .find(|finding| finding.kind() == RuleKind::UnconstrainedLessThan)
            .unwrap();
        let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
        let report = finding.to_report(&sources).unwrap();
        assert_eq!(report.id(), "CS0014");
        assert_eq!(report.category(), &MessageCategory::Warning);
        assert_eq!(
            report.message(),
            &format!("Comparator input {value} is outside the proved safe range [0, 256).")
        );
        assert_eq!(&loaded.files[0].text[report.primary()[0].range.clone()], value);
    }
}

#[test]
fn exact_safe_range_boundary_and_both_input_positions_are_checked() {
    for (left, right, expected) in
        [("255", "1", 0), ("256", "1", 1), ("255", "256", 1), ("256", "256", 2)]
    {
        let (_, result) = inspect(&source(left, right, "<=="), Curve::Bn254, None);
        assert_eq!(count(&result), expected, "{left}/{right}: {:?}", result.abstentions());
    }
}

#[test]
fn witness_constants_and_near_matching_bodies_do_not_establish_comparator_evidence() {
    let field = FieldContext::for_curve(Curve::Bn254);
    let outside = field.canonical((-254).into()).as_bigint().to_string();
    let generated = source(&outside, "1", "<==");
    for variant in [
        source(&outside, "1", "<--"),
        generated.replace("+(1<<n)", "+255"),
        generated.replace("1-d.bits[n]", "1-d.bits[n-1]"),
        generated.replace("bits[i]*(bits[i]-1)===0;", ""),
        generated.replace("value===sum", "value===sum+1"),
    ] {
        assert_eq!(count(&inspect(&variant, Curve::Bn254, None).1), 0, "{variant}");
    }
}

#[test]
fn canonical_saved_corpus_emit_has_terminal_sarif_spans_and_filters() {
    let source = include_str!("../../tests/warnings/cases/unconstrained_less_than_emit.circom");
    let (loaded, result) = inspect(source, Curve::Bn254, None);
    assert_eq!(count(&result), 1, "{:?}", result.abstentions());
    let findings: Vec<_> = result
        .findings()
        .iter()
        .filter(|finding| finding.kind() == RuleKind::UnconstrainedLessThan)
        .cloned()
        .collect();
    let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
    let output = loaded.files[0].path.with_extension("sarif.json");
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Info, &[], &output).unwrap(),
        (1, 1)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
    let item = &sarif["runs"][0]["results"][0];
    assert_eq!(item["ruleId"], "CS0014");
    assert_eq!(item["level"], "warning");
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Info, &["CS0014"], &output).unwrap(),
        (0, 0)
    );
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Error, &[], &output).unwrap(),
        (0, 0)
    );
}

fn literal_source(left: &str, right: &str, assignment: &str) -> String {
    source(left, right, assignment).replace("(1<<n)", "256").replace("d.bits[n]", "d.bits[8]")
}

#[test]
fn literal_specialization_preserves_the_same_comparator_relation() {
    for curve in [Curve::Bn254, Curve::Goldilocks, Curve::Bls12_381] {
        let field = FieldContext::for_curve(curve.clone());
        let value = field.canonical((-254).into()).as_bigint().to_string();
        let (_, result) = inspect(&literal_source(&value, "1", "<=="), curve, None);
        assert_eq!(count(&result), 1, "{:?}", result.abstentions());
    }
    for (left, right, expected) in
        [("255", "1", 0), ("256", "1", 1), ("255", "256", 1), ("256", "256", 2)]
    {
        let (_, result) = inspect(&literal_source(left, right, "<=="), Curve::Bn254, None);
        assert_eq!(count(&result), expected, "{left}/{right}: {:?}", result.abstentions());
    }
}

#[test]
fn literal_comparator_rejects_witness_values_and_near_matching_relations() {
    let source = literal_source("256", "1", "<==");
    for source in [
        literal_source("256", "1", "<--"),
        source.replace("operands[0]+256-operands[1]", "operands[0]+255-operands[1]"),
        source.replace("1-d.bits[8]", "1-d.bits[7]"),
        source.replace("bits[i]*(bits[i]-1)===0;", ""),
        source.replace("value===sum;", "value===sum+1;"),
        source.replace("c.operands[0]<==256;", "signal x;x<--256;c.operands[0]<==x;"),
    ] {
        let (_, result) = inspect(&source, Curve::Bn254, None);
        assert_eq!(count(&result), 0, "{source}: {:?}", result.abstentions());
    }
}

#[test]
fn every_scope_extra_equation_can_reject_the_comparator_candidate() {
    let source = literal_source("256", "1", "<==");
    for source in [
        source.replace("out<==c.answer;", "out<==c.answer;out===1;"),
        source.replace("answer<==1-d.bits[8];", "answer<==1-d.bits[8];answer===1;"),
        source.replace("value===sum;", "value===sum;bits[8]===0;"),
    ] {
        let (_, result) = inspect(&source, Curve::Bn254, None);
        assert_eq!(count(&result), 0, "{source}: {:?}", result.abstentions());
    }
    for source in [
        source.replace("out<==c.answer;", "out<==c.answer;out===0;"),
        source.replace("answer<==1-d.bits[8];", "answer<==1-d.bits[8];answer===0;"),
        source.replace("value===sum;", "value===sum;bits[8]===1;"),
    ] {
        let (_, result) = inspect(&source, Curve::Bn254, None);
        assert_eq!(count(&result), 1, "{source}: {:?}", result.abstentions());
    }
}

#[test]
fn literal_comparator_incomplete_bindings_control_and_local_budgets_abstain() {
    let source = literal_source("256", "1", "<==");
    for source in [
        source.replace("c.operands[1]<==1;", ""),
        source.replace("c.operands[1]<==1;", "c.operands[1]<==1;c.operands[1]<==1;"),
        source.replace("c.operands[1]<==1;", "c.operands[2]<==1;"),
        source
            .replace("component c=Compare(8);", "signal input k;component c=Compare(8);")
            .replace("c.operands[0]<==256;", "c.operands[k]<==256;"),
        source.replace("out<==c.answer;", "out<==c.answer;assert(0);"),
        source.replace("value===sum;", "value===sum;var bad=1/0;"),
    ] {
        let (_, result) = inspect(&source, Curve::Bn254, None);
        assert_eq!(count(&result), 0, "{source}: {:?}", result.abstentions());
        assert!(result
            .abstentions()
            .iter()
            .any(|item| item.kind == RuleKind::UnconstrainedLessThan));
    }
    for budget in [0, 1, 2, 5, 10] {
        let (_, result) = inspect(&source, Curve::Bn254, Some(budget));
        assert_eq!(count(&result), 0);
    }
}

#[test]
fn exact_width_boundaries_keep_comparison_encoding_below_the_selected_field() {
    for (width, expected) in [(0_usize, 2_usize), (62, 1), (63, 0)] {
        let limit = 1_u128 << width;
        let source = literal_source(&limit.to_string(), "1", "<==")
            .replace("Compare(8)", &format!("Compare({width})"))
            .replace("operands[0]+256-operands[1]", &format!("operands[0]+{limit}-operands[1]"))
            .replace("d.bits[8]", &format!("d.bits[{width}]"));
        let (_, result) = inspect(&source, Curve::Goldilocks, None);
        assert_eq!(count(&result), expected, "width {width}: {:?}", result.abstentions());
    }
}

#[test]
fn generated_control_and_complete_constructor_scope_are_required() {
    let source = literal_source("256", "1", "<==");
    for (from, equation) in [
        ("out<==c.answer;", "out===1;"),
        ("answer<==1-d.bits[8];", "answer===1;"),
        ("value===sum;", "bits[8]===0;"),
    ] {
        for (guard, expected) in [("0", 1), ("1", 0)] {
            let source = source.replace(from, &format!("{from}if({guard}){{{equation}}}"));
            let (_, result) = inspect(&source, Curve::Bn254, None);
            assert_eq!(count(&result), expected, "{source}: {:?}", result.abstentions());
        }
        let source = source.replace(from, &format!("{from}signal input k;if(k){{{equation}}}"));
        let (_, result) = inspect(&source, Curve::Bn254, None);
        assert_eq!(count(&result), 0, "{source}: {:?}", result.abstentions());
    }
    for source in [
        source.replace("component c=Compare(8);", "component c=Compare(8);component spare;"),
        source
            .replace("component d=Decompose(n+1);", "component d=Decompose(n+1);component spare;"),
        source.replace(
            "component d=Decompose(n+1);",
            "component d=Decompose(n+1);component other=Decompose(1);other.value<==0;",
        ),
        source.replace("out<==c.answer;", "out<==c.answer;signal local;local===0;"),
    ] {
        let (_, result) = inspect(&source, Curve::Bn254, None);
        assert_eq!(count(&result), 0, "{source}: {:?}", result.abstentions());
    }
}

#[test]
fn literal_comparator_renderer_preserves_evidence_spans_and_source_filters() {
    let source = literal_source("256", "1", "<==");
    let (loaded, result) = inspect(&source, Curve::Bn254, None);
    let findings: Vec<_> = result
        .findings()
        .iter()
        .filter(|finding| finding.kind() == RuleKind::UnconstrainedLessThan)
        .cloned()
        .collect();
    assert_eq!(findings.len(), 1);
    let sources = SourceMap::from_loaded(&loaded, &[loaded.files[0].id]).unwrap();
    let report = findings[0].to_report(&sources).unwrap();
    assert_eq!(report.secondary().len(), 7);
    for marker in ["bits[i]*(bits[i]-1)", "value===sum", "d.value<==", "answer<==", "out<=="] {
        assert!(report
            .secondary()
            .iter()
            .any(|label| source[label.range.clone()].contains(marker)));
    }
    let offset = source.find("c.operands[0]<==256;").unwrap() + "c.operands[0]<==".len();
    assert_eq!(report.primary()[0].range, offset..offset + 3);
    let output = loaded.files[0].path.with_extension("sarif.json");
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Info, &[], &output).unwrap(),
        (1, 1)
    );
    let sarif: Value = serde_json::from_str(&fs::read_to_string(&output).unwrap()).unwrap();
    let item = &sarif["runs"][0]["results"][0];
    assert_eq!(item["ruleId"], "CS0014");
    assert_eq!(item["level"], "warning");
    assert_eq!(
        item["message"]["text"],
        "Comparator input 256 is outside the proved safe range [0, 256)."
    );
    let region = &item["locations"][0]["physicalLocation"]["region"];
    assert_eq!(region["startLine"], 1);
    assert_eq!(region["startColumn"], offset + 1);
    assert_eq!(region["endColumn"], offset + 4);
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Info, &["CS0014"], &output).unwrap(),
        (0, 0)
    );
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Error, &[], &output).unwrap(),
        (0, 0)
    );
    let sources = SourceMap::from_loaded(&loaded, &[]).unwrap();
    assert_eq!(
        support::render(&findings, &sources, MessageCategory::Info, &[], &output).unwrap(),
        (0, 0)
    );
}

#[test]
fn exact_numeric_aliases_of_signals_do_not_certify_generation_control() {
    let source = literal_source("256", "1", "<==");
    for expression in ["operands[0]", "One(operands[0])", "One(Alias(operands[0]))"] {
        let source = format!(
            "function One(x){{return 1;}}function Alias(x){{return x;}}{}",
            source.replace(
                "answer<==1-d.bits[8];",
                &format!(
                    "var choice={expression};var alias=choice;if(alias){{answer<==1-d.bits[8];}}"
                ),
            )
        );
        let (_, result) = inspect(&source, Curve::Bn254, None);
        assert_eq!(count(&result), 0, "{source}: {:?}", result.abstentions());
    }
}

#[test]
fn pure_helper_guard_retains_typed_abstention_when_shape_is_unresolved() {
    let source = literal_source("256", "1", "<==");
    let source = format!(
        "function One(x){{return 1;}}{}",
        source.replace(
            "answer<==1-d.bits[8];",
            "var choice=One(3);if(choice){answer<==1-d.bits[8];}"
        ),
    );
    let (_, result) = inspect(&source, Curve::Bn254, None);
    assert_eq!(count(&result), 0, "{:?}", result.abstentions());
    assert!(result.abstentions().iter().any(|abstention| {
        let AbstentionReason::Summary(blockers) = &abstention.reason else { return false };
        abstention.kind == RuleKind::UnconstrainedLessThan
            && blockers.iter().any(|blocker| {
                if let SummaryBlocker::LocalFacts(facts) = blocker {
                    !facts.is_empty()
                } else {
                    false
                }
            })
    }));
}

#[test]
fn completed_scopes_discharge_only_resolved_template_body_regions() {
    let canonical = source("256", "1", "<==");
    let disconnected = format!("template Incomplete(){{var unknown=Missing();}}{canonical}");
    let (_, result) = inspect(&disconnected, Curve::Bn254, None);
    assert_eq!(count(&result), 1, "{:?}", result.abstentions());
    for (needle, addition) in [
        ("component d=Decompose(n+1);", "var unknown=Identity(operands[0]);"),
        ("var sum=0;", "var unknown=Identity(value);"),
    ] {
        let unresolved = format!(
            "function Identity(x){{return x;}}{}",
            canonical.replace(needle, &format!("{needle}{addition}")),
        );
        let (loaded, result) = inspect(&unresolved, Curve::Bn254, None);
        let lifted = lift_project(&loaded);
        assert!(lifted
            .incomplete
            .iter()
            .any(|region| { region.reason == parser::hir::IncompleteReason::UnknownType }));
        assert_eq!(count(&result), 0, "{:?}", result.abstentions());
        assert!(result.abstentions().iter().any(|a| a.kind == RuleKind::UnconstrainedLessThan));
    }
}

#[test]
fn additional_scalar_comparator_inputs_obey_the_schema_budget() {
    let canonical = source("256", "1", "<==");
    for extra in [1, 2, 510, 511, 512] {
        let mut declarations = String::new();
        let mut assignments = String::new();
        for index in 0..extra {
            declarations.push_str(&format!("signal input extra{index};"));
            assignments.push_str(&format!("c.extra{index}<==0;"));
        }
        let source = canonical
            .replace(
                "signal input operands[2];",
                &format!("signal input operands[2];{declarations}"),
            )
            .replace("out<==c.answer;", &format!("{assignments}out<==c.answer;"));
        let (_, result) = inspect(&source, Curve::Bn254, None);
        assert_eq!(count(&result), 0, "extra inputs: {extra}");
        assert!(result.abstentions().iter().any(|abstention| {
            let AbstentionReason::Summary(blockers) = &abstention.reason else { return false };
            abstention.kind == RuleKind::UnconstrainedLessThan
                && blockers.contains(&SummaryBlocker::ContextBudget)
        }));
    }
}

#[test]
fn repeated_source_accesses_keep_each_output_read_site_bounds() {
    let canonical = source("256", "1", "<==");
    for (bound, expected) in [("9", 1), ("10", 0)] {
        let source = canonical.replace(
            "answer<==1-d.bits[n];",
            &format!("for(var j=0;j<{bound};j++){{log(d.bits[j]);}}answer<==1-d.bits[n];"),
        );
        let (_, result) = inspect(&source, Curve::Bn254, None);
        assert_eq!(count(&result), expected, "{bound}: {:?}", result.abstentions());
    }
}
