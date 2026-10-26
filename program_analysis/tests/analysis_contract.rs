// Tests intentionally fail by panicking; fixtures retain explicit independent expectations.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]

use std::collections::BTreeSet;
use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::{analyze, FactBlocker, FieldContext, Incidence, Range};
use circomspect_program_analysis::interprocedural::{
    ArgumentValue, CallOwner, CallReachability, ContextEvidence, FunctionEffect, ProjectAnalysis,
    ReturnEvidence, SummaryBlocker, WitnessProvenance,
};
use circomspect_program_analysis::rules::{RuleContext, RuleContextError};
use parser::hir::{lift_project, DefinitionRef, ExprId, LiftedProject};
use parser::frontend::{load_sources, Span, Version, VersionPolicy};
use program_structure::utils::constants::Curve;
use serde_json::{json, Value};

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-analysis-contract-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(
        std::slice::from_ref(&path),
        std::slice::from_ref(&directory),
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    let lifted = lift_project(&loaded);
    fs::remove_file(path).unwrap();
    fs::remove_dir(directory).unwrap();
    lifted
}

fn range_record(range: &Range) -> Value {
    match range {
        Range::Unreachable => json!({ "kind": "unreachable" }),
        Range::Canonical => json!({ "kind": "canonical" }),
        Range::Exact(value) => json!({ "kind": "exact", "value": value.as_bigint().to_string() }),
    }
}

fn span_record(span: Span) -> Value {
    json!({ "source": span.source().index(), "start": span.start(), "end": span.end() })
}

fn expression(project: &LiftedProject, source: &str, marker: &str) -> ExprId {
    let start = source.find(marker).unwrap();
    project
        .hir
        .expressions()
        .iter()
        .find(|expression| {
            expression.span.start() == start && expression.span.end() == start + marker.len()
        })
        .unwrap()
        .id
}

fn local_records() -> Vec<Value> {
    let source = concat!(
        "function Other(){return 91;}",
        "template Check(){signal input a;signal output y;y<==a+1;if(0){var dead=7;}}"
    );
    let lifted = fixture(source);
    let definition = lifted.hir.definition("Check").unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&lifted.hir, &cfg, &field, None).unwrap();
    let live = expression(&lifted, source, "a+1");
    let dead = expression(&lifted, source, "7");
    let unobserved = expression(&lifted, source, "91");
    let missing = BTreeSet::from([FactBlocker::MissingExit]);
    assert_eq!(facts.range(dead).unavailable(), Some(&missing));
    assert_eq!(facts.range(unobserved).unavailable(), Some(&missing));
    assert_eq!(facts.reachable_expression(unobserved).unavailable(), Some(&missing));
    let pending = analyze(&lifted.hir, &cfg, &field, Some(0)).unwrap();
    assert_eq!(pending.range(live).unavailable(), Some(&missing));
    assert_eq!(
        pending.reachable_expression(live).unavailable(),
        Some(&BTreeSet::from([FactBlocker::Budget(cfg.entry())]))
    );
    vec![
        json!({ "id": "local.unknown", "state": "certified",
            "range": range_record(facts.range(live).certified().unwrap()),
            "reachable": facts.reachable_expression(live).certified().unwrap() }),
        json!({ "id": "local.unreachable", "state": "unavailable",
            "blockers": ["MissingExit"],
            "reachable": facts.reachable_expression(dead).certified().unwrap() }),
        json!({ "id": "local.unobserved", "state": "unavailable",
            "blockers": ["MissingExit"], "reachability_blockers": ["MissingExit"] }),
        json!({ "id": "local.pending", "state": "unavailable",
            "blockers": ["MissingExit"], "reachability_blockers": [{ "Budget": "cfg.entry" }] }),
    ]
}

fn function_records() -> Vec<Value> {
    let source = concat!(
        "function Exact(n){return n+2;}",
        "function Conditional(){var t=Missing();return 7;}",
        "function Empty(){return 7;}",
        "function Cycle(){log(1);return Cycle();}",
        "function Noisy(){assert(1);log(7);return 7;}"
    );
    let lifted = fixture(source);
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let mut records = Vec::new();
    for name in ["Exact", "Conditional", "Empty", "Noisy"] {
        let definition = lifted.hir.definition(name).unwrap();
        let DefinitionRef::Function(function) = definition else { panic!("function {name}") };
        let context = if name == "Exact" {
            provider.context_for(definition, vec![ArgumentValue::Scalar(field.canonical(5.into()))])
        } else {
            provider.symbolic_context_for(definition)
        }
        .unwrap();
        let summary = provider.function(function, &context);
        assert_eq!(summary, provider.function(function, &context));
        let summary = summary.certified().unwrap_or_else(|| panic!("{name}: {summary:?}"));
        let (coverage, value) = match summary.return_evidence() {
            ReturnEvidence::Complete(value) => ("complete", value),
            ReturnEvidence::Conditional(value) => ("conditional", value),
        };
        records.push(json!({
            "id": format!("return.{name}"), "state": "certified", "coverage": coverage,
            "value": range_record(value), "dependencies": summary.input_dependencies()
        }));
        let effects = provider.function_effects(function, &context);
        assert_eq!(effects, provider.function_effects(function, &context));
        if name == "Conditional" {
            assert_eq!(
                effects.unavailable(),
                Some(&BTreeSet::from([SummaryBlocker::ExternalSummary]))
            );
            records.push(json!({
                "id": "effects.Conditional", "state": "unavailable", "blockers": ["ExternalSummary"]
            }));
        } else {
            let effects = effects.certified().unwrap();
            records.push(json!({
                "id": format!("effects.{name}"), "state": "certified",
                "empty": effects.is_empty(), "assert": effects.contains(FunctionEffect::Assert),
                "log": effects.contains(FunctionEffect::Log)
            }));
        }
    }
    let definition = lifted.hir.definition("Cycle").unwrap();
    let DefinitionRef::Function(function) = definition else { panic!("Cycle") };
    let context = provider.symbolic_context_for(definition).unwrap();
    let summary = provider.function(function, &context);
    assert_eq!(summary.unavailable(), Some(&BTreeSet::from([SummaryBlocker::RecursiveCycle])));
    records.push(json!({
        "id": "return.Cycle", "state": "unavailable", "blockers": ["RecursiveCycle"]
    }));
    let effects = provider.function_effects(function, &context);
    let effects = effects.certified().unwrap();
    records.push(json!({
        "id": "effects.Cycle", "state": "certified", "empty": effects.is_empty(),
        "assert": effects.contains(FunctionEffect::Assert), "log": effects.contains(FunctionEffect::Log)
    }));
    records
}

fn incidence_record(incidence: Incidence) -> &'static str {
    match incidence {
        Incidence::Zero => "zero",
        Incidence::May => "may",
        Incidence::Must => "must",
    }
}

fn port_records() -> Vec<Value> {
    let source = "template T(){signal input x;signal output y,z;y<--x;z<==1;}";
    let lifted = fixture(source);
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let DefinitionRef::Template(template) = definition else { panic!("template T") };
    let context = provider.symbolic_context_for(definition).unwrap();
    let mut records = Vec::new();
    for port in &lifted.hir.template(template).unwrap().ports {
        let symbol = lifted.hir.port(*port).unwrap().symbol;
        let name = &lifted.hir.symbol(symbol).unwrap().name;
        let summary = provider.template_port(template, &context, *port);
        assert_eq!(summary, provider.template_port(template, &context, *port));
        let summary = summary.certified().unwrap();
        assert_eq!(summary.context(), &context);
        assert_eq!(summary.port(), *port);
        let read = provider.template_port_read(template, &context, *port);
        let writes = provider.template_port_witnesses(template, &context, *port);
        let mut origins = Vec::new();
        for write in writes.certified().unwrap() {
            let origin = write.origin();
            let provenance = match write.provenance() {
                WitnessProvenance::WitnessOnly => "witness",
                WitnessProvenance::GeneratedConstraint => "generated",
            };
            let expression =
                origin.expression.map(|id| span_record(lifted.hir.expression(id).unwrap().span));
            origins.push(json!({
                "span": span_record(origin.span), "expression": expression,
                "block": span_record(lifted.hir.block(origin.block).unwrap().span),
                "effect": origin.effect_index, "provenance": provenance
            }));
        }
        records.push(json!({
            "id": format!("port.{name}"), "state": "certified",
            "indices": summary.indices(), "incidence": incidence_record(summary.incidence()),
            "fixed": summary.fixed_value().map(|value| value.as_bigint().to_string()),
            "read": read.certified().unwrap(), "writes": origins
        }));
    }
    records
}

fn array_port_records() -> Vec<Value> {
    let lifted = fixture("template T(){signal output out[2];out[0]<==1;out[1]<--2;}");
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let DefinitionRef::Template(template) = definition else { panic!("template T") };
    let port = lifted.hir.template(template).unwrap().ports[0];
    let context = provider.symbolic_context_for(definition).unwrap();
    let mut records = Vec::new();
    for index in [0, 1] {
        let summary = provider.template_port_at(template, &context, port, &[index]);
        assert_eq!(summary, provider.template_port_at(template, &context, port, &[index]));
        let summary = summary.certified().unwrap();
        assert_eq!(summary.indices(), [index]);
        records.push(json!({
            "id": format!("port.array.{index}"), "state": "certified",
            "indices": summary.indices(), "incidence": incidence_record(summary.incidence()),
            "fixed": summary.fixed_value().map(|value| value.as_bigint().to_string())
        }));
    }
    records
}

fn context_records() -> Vec<Value> {
    let source = "function F(n){return n;}";
    let first = fixture(source);
    let second = fixture(source);
    let bn = ProjectAnalysis::build(&first, Curve::Bn254).unwrap();
    let twin = ProjectAnalysis::build(&second, Curve::Bn254).unwrap();
    let gold = ProjectAnalysis::build(&first, Curve::Goldilocks).unwrap();
    let definition = first.hir.definition("F").unwrap();
    let local = bn.symbolic_context_for(definition).unwrap();
    let same = bn.symbolic_context_for(definition).unwrap();
    let foreign = twin.symbolic_context_for(second.hir.definition("F").unwrap()).unwrap();
    let other_curve = gold.symbolic_context_for(definition).unwrap();
    let contexts = [&local, &same, &foreign, &other_curve];
    let mut equality = Vec::new();
    for left in contexts {
        let mut row = Vec::new();
        for right in contexts {
            row.push(left == right);
        }
        equality.push(row);
    }
    assert_eq!(bn.check_context(&foreign), Err(SummaryBlocker::WrongContext));
    assert_eq!(bn.check_context(&other_curve), Err(SummaryBlocker::WrongContext));
    assert_ne!(first.hir.identity(), second.hir.identity());
    vec![json!({
        "id": "context.identity", "slots": ["first", "first_again", "source_twin", "gold"],
        "equal": equality, "foreign_blockers": ["WrongContext", "WrongContext"]
    })]
}

fn child_evidence(provider: &ProjectAnalysis<'_>, name: &str) -> ContextEvidence {
    let definition = provider.hir().definition(name).unwrap();
    let caller = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(provider.hir(), definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("reachable child")
    };
    provider.call_evidence(&call, &facts, &caller).unwrap()
}

fn ancestry_records() -> Vec<Value> {
    let lifted = fixture(concat!(
        "template Leaf(n){var x=n;}",
        "template Left(){component c=Leaf(7);}",
        "template Right(){component c=Leaf(7);}"
    ));
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let left = child_evidence(&provider, "Left");
    let right = child_evidence(&provider, "Right");
    let cfg = build_cfg(&lifted.hir, left.context().definition()).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &left, None).unwrap();
    let other_facts = provider.analyze_for_evidence(&cfg, &right, None).unwrap();
    assert_eq!(
        RuleContext::new(&facts, &provider, &right).err(),
        Some(RuleContextError::MismatchedFacts(SummaryBlocker::WrongContext))
    );
    let left_context = RuleContext::new(&facts, &provider, &left).unwrap();
    let right_context = RuleContext::new(&other_facts, &provider, &right).unwrap();
    let mut paths = Vec::new();
    for context in [&left_context, &right_context] {
        let mut path = Vec::new();
        for site in context.call_path() {
            path.push(span_record(site.span()));
        }
        paths.push(path);
    }
    vec![json!({
        "id": "context.ancestry", "slots": ["left_call", "right_call"],
        "equal_contexts": left.context() == right.context(),
        "equal_paths": left_context.call_path() == right_context.call_path(), "paths": paths,
        "cross_facts_blocker": "WrongContext"
    })]
}

#[test]
fn scoped_analysis_records_match_the_frozen_contract() {
    let mut records = local_records();
    records.extend(function_records());
    records.extend(port_records());
    records.extend(array_port_records());
    records.extend(context_records());
    records.extend(ancestry_records());
    let observed = json!({ "schema": 1, "records": records });
    if let Ok(path) = std::env::var("CIRCOMSPECT_OBSERVATION_PATH") {
        let output = fs::OpenOptions::new().write(true).create_new(true).open(path).unwrap();
        serde_json::to_writer_pretty(output, &observed).unwrap();
    }
    let expected: Value =
        serde_json::from_str(include_str!("fixtures/analysis_contract.json")).unwrap();
    assert_eq!(observed, expected);
}
