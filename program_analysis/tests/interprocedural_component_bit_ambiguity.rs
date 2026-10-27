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
use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::{FieldContext, NoBitAmbiguityCertificate};
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ComponentBitAmbiguity, ComponentBitAmbiguityOutcome,
    ProjectAnalysis,
};
use num_bigint_dig::BigInt;
use parser::hir::{lift_project, AccessPath, AccessStep, ArrayIndex, HirProject, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-component-models-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

fn source(parent: &str, child: &str) -> String {
    source_width(64, parent, child)
}

fn source_width(width: usize, parent: &str, child: &str) -> String {
    let mut source = "template Convert(n){signal input in;signal output bits[n];".to_string();
    let mut sum = String::new();
    let mut weight = BigInt::from(1);
    for index in 0..width {
        source.push_str(&format!("bits[{index}]<--0;bits[{index}]*(bits[{index}]-1)===0;"));
        if index != 0 {
            sum.push('+');
        }
        sum.push_str(&format!("{weight}*bits[{index}]"));
        weight *= 2;
    }
    source.push_str(&format!(
        "in==={sum};{child}}}template Parent(){{{parent}}}component main=Parent();"
    ));
    source
}

fn path(hir: &HirProject, name: &str, index: Option<usize>) -> AccessPath {
    let symbol = hir.symbols().iter().find(|symbol| symbol.name == name).unwrap();
    let steps = index
        .into_iter()
        .map(|index| AccessStep::Index {
            index: ArrayIndex::Constant(index.to_string()),
            span: symbol.span,
        })
        .collect();
    AccessPath {
        root: symbol.id,
        terminal: symbol.id,
        steps,
        component_input: false,
        component_output: false,
        span: symbol.span,
    }
}

#[derive(Clone, Copy)]
enum QueryForm {
    Paths,
    Handles,
}

fn inspect(source: &str, budget: Option<usize>) -> Option<ComponentBitAmbiguityOutcome> {
    inspect_with(source, budget, Curve::Goldilocks, 64, QueryForm::Paths)
}

fn inspect_with(
    source: &str,
    budget: Option<usize>,
    curve: Curve,
    width: usize,
    form: QueryForm,
) -> Option<ComponentBitAmbiguityOutcome> {
    let project = fixture(source);
    let provider = ProjectAnalysis::build(&project, curve).unwrap();
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(main.id(), &project.hir)
    else {
        return None;
    };
    let caller = provider.contexts().main_evidence(&call).ok()?;
    let definition = project.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &caller, budget).ok()?;
    let convert = project.hir.definition("Convert").unwrap();
    let site = provider
        .graph()
        .calls_from(CallOwner::Definition(definition))
        .into_iter()
        .find(|site| site.resolved() == Some(convert))?;
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        return None;
    };
    let callee = provider.contexts().call_evidence(&call, &facts, &caller).ok()?;
    let cfg = build_cfg(&project.hir, call.callee()).unwrap();
    let child = provider.contexts().analyze_for_evidence(&cfg, &callee, None).ok()?;
    let port = project
        .hir
        .ports()
        .iter()
        .find(|port| project.hir.symbol(port.symbol).unwrap().name == "bits")
        .unwrap();
    let local = child.port_handle(port.id, &[0]).ok()?;
    let applied =
        provider.components().apply_component_local_output(&facts, &caller, &call, &local);
    let applied = applied.certified()?;
    let input = path(&project.hir, "in", None);
    let bits: Vec<_> = (0..width).map(|index| path(&project.hir, "bits", Some(index))).collect();
    assert!(
        provider
            .templates()
            .template_bit_ambiguity(&child, &callee, &input, &bits)
            .unavailable()
            .is_some(),
        "standalone called scope must remain blocked"
    );
    let result = match form {
        QueryForm::Paths => {
            provider.components().component_bit_ambiguity(&facts, applied, &input, &bits)
        }
        QueryForm::Handles => {
            let input_port = project.hir.ports().iter().find(|port| port.symbol == input.root)?;
            let input = child.port_handle(input_port.id, &[]).ok()?;
            let bits = (0..width)
                .map(|index| child.port_handle(port.id, &[index]))
                .collect::<Result<Vec<_>, _>>()
                .ok()?;
            let context =
                circomspect_program_analysis::rules::RuleContext::new(&facts, &provider, &caller)
                    .ok()?;
            context.component_bit_ambiguity_handles(applied, &input, &bits)
        }
    };
    result.certified().cloned()
}

fn certificate(result: Option<&ComponentBitAmbiguityOutcome>) -> &ComponentBitAmbiguity {
    let Some(ComponentBitAmbiguityOutcome::Proved(proof)) = result else {
        panic!("expected two complete closure models: {result:?}");
    };
    proof
}

fn verify_pair(proof: &ComponentBitAmbiguity, input: i64) {
    let field = FieldContext::for_curve(Curve::Goldilocks);
    let input = field.canonical(input.into());
    assert_eq!(proof.input_value(), &input);
    assert_eq!(proof.applied_port().callee_evidence(), proof.decomposition().context());
    assert_ne!(proof.representations()[0].bits(), proof.representations()[1].bits());
    for (representation, assignment) in proof.representations().iter().zip(proof.assignments()) {
        let mut integer = BigInt::from(0);
        let mut weight = BigInt::from(1);
        for (bit, key) in representation.bits().iter().zip(proof.decomposition().bits()) {
            let value = field.canonical(i32::from(*bit).into());
            assert_eq!(assignment.callee().get(key), Some(&value));
            assert!(field.is_zero(
                &field.multiply(&value, &field.subtract(&value, &field.canonical(1.into())))
            ));
            if *bit {
                integer += &weight;
            }
            weight *= 2;
        }
        assert_eq!(&integer.to_biguint().unwrap(), representation.integer());
        assert_eq!(field.canonical(integer), input);
        assert_eq!(assignment.callee().get(proof.decomposition().input()), Some(&input));
        assert!(assignment.caller().values().all(|value| value == &input));
    }
    assert_eq!(proof.caller_constraint_origins().len(), 1);
    assert_eq!(proof.callee_constraint_origins().len(), 65);
    assert_eq!(proof.input_binding_origins().len(), 1);
}

#[test]
fn generated_literal_and_free_parent_signal_bindings_prove_complete_models() {
    for (parent, input) in [
        ("component c=Convert(64);c.in<==0;", 0),
        ("component c=Convert(64);c.in<==1;", 1),
        ("signal input x;component c=Convert(64);c.in<==x;", 0),
    ] {
        let result = inspect(&source(parent, ""), None);
        verify_pair(certificate(result.as_ref()), input);
    }
}

#[test]
fn parent_restrictive_equations_are_checked_after_matching_child_relations() {
    let source = source("component c=Convert(64);c.in<==0;c.bits[0]===0;", "");
    assert_eq!(
        inspect(&source, None),
        Some(ComponentBitAmbiguityOutcome::NoCertificate(
            NoBitAmbiguityCertificate::CandidatesRejected
        ))
    );
}

#[test]
fn missing_duplicate_witness_and_opaque_input_bindings_abstain() {
    for parent in [
        "component c=Convert(64);",
        "component c=Convert(64);c.in<==0;c.in<==0;",
        "component c=Convert(64);c.in<--0;",
        "signal input x;component c=Convert(64);c.in<==x+1;",
        "signal input x;component c=Convert(64);c.in<==Missing(x);",
    ] {
        assert!(inspect(&source(parent, ""), None).is_none(), "{parent}");
    }
}

#[test]
fn additional_instances_and_unclosed_children_cannot_borrow_the_selected_pair() {
    for parent in [
        "component c=Convert(64);c.in<==0;component d=Convert(64);d.in<==0;",
        "component c[2];c[0]=Convert(64);c[1]=Convert(64);c[0].in<==0;c[1].in<==1;",
        "component c=Convert(64);c.in<==0;component d=Missing();",
    ] {
        assert!(inspect(&source(parent, ""), None).is_none(), "{parent}");
    }
    let nested =
        source("component c=Convert(64);c.in<==0;", "component d=Extra();") + "template Extra(){}";
    assert!(inspect(&nested, None).is_none());
}

#[test]
fn failures_unknown_control_and_incomplete_budgets_withhold_closure_models() {
    for (parent, child) in [
        ("component c=Convert(64);c.in<==0;assert(0);", ""),
        ("component c=Convert(64);c.in<==0;", "assert(0);"),
        ("component c=Convert(64);c.in<==0;", "signal s;signal t;t<--s;s<--0;"),
        ("signal input n;component c=Convert(n);c.in<==0;", "if(n){bits[0]===0;}"),
        ("signal input n;component c=Convert(64);c.in<==0;if(n){c.bits[0]===0;}", ""),
    ] {
        assert!(inspect(&source(parent, child), None).is_none(), "{parent} / {child}");
    }
    let valid = source("component c=Convert(64);c.in<==0;", "");
    for limit in [0, 1, 4, 8] {
        assert!(inspect(&valid, Some(limit)).is_none(), "{limit}");
    }
}

#[test]
fn numeric_variable_results_do_not_hide_signal_dependent_generation_control() {
    for assignments in ["var a=x;var b=a;", "var a=Ignore(x);var b=a;"] {
        let parent = format!(
            "signal input x;{assignments}component c=Convert(64);c.in<==0;\
             if(b){{c.bits[0]===0;}}"
        );
        let source = source(&parent, "") + "function Ignore(value){return 0;}";
        assert!(inspect(&source, None).is_none(), "{source}");
    }
}

#[test]
fn checked_handles_support_parameterized_canonical_loop_children() {
    let source = "template Convert(n){signal input in;signal output bits[n];var sum=0;        for(var i=0;i<n;i++){bits[i]<--(in >> i)&1;bits[i]*(bits[i]-1)===0;        sum+=bits[i]*(2**i);}in===sum;}        template Parent(){signal input x;component c=Convert(64);c.in<==x;}        component main=Parent();";
    let result = inspect_with(source, None, Curve::Goldilocks, 64, QueryForm::Handles);
    verify_pair(certificate(result.as_ref()), 0);
    assert_eq!(
        inspect_with(
            &source.replace("Convert(64)", "Convert(63)"),
            None,
            Curve::Goldilocks,
            63,
            QueryForm::Handles
        ),
        Some(ComponentBitAmbiguityOutcome::NoCertificate(
            NoBitAmbiguityCertificate::WidthBelowFieldModulus
        ))
    );
}

#[test]
fn unrelated_semantic_error_does_not_hide_a_complete_main_child_query() {
    let base = source_width(1, "component c=Convert(1);c.in<==0;", "in*(in-1)===0;");
    for body in ["function Broken(){return Missing();}", "template Broken(){var unused=Missing();}"]
    {
        let unrelated =
            base.replace("component main=Parent();", &format!("{body}component main=Parent();"));
        assert_eq!(
            inspect_with(&unrelated, None, Curve::Goldilocks, 1, QueryForm::Handles),
            Some(ComponentBitAmbiguityOutcome::NoCertificate(
                NoBitAmbiguityCertificate::WidthBelowFieldModulus
            )),
            "{body}"
        );
    }

    let child = source_width(1, "component c=Convert(1);c.in<==0;", "var bad=Missing();");
    assert!(inspect_with(&child, None, Curve::Goldilocks, 1, QueryForm::Handles).is_none());
    let include = format!("include \"missing-model-scope.circom\";{base}");
    assert!(inspect_with(&include, None, Curve::Goldilocks, 1, QueryForm::Handles).is_none());
    let header = base.replace(
        "component main=Parent();",
        "function Broken(x,x){return x;}component main=Parent();",
    );
    assert!(inspect_with(&header, None, Curve::Goldilocks, 1, QueryForm::Handles).is_none());
    let main = base.replace("component main=Parent();", "component main=Missing();");
    assert!(inspect_with(&main, None, Curve::Goldilocks, 1, QueryForm::Handles).is_none());
    let connected = base.replace(
        "component main=Parent();",
        "function Broken(){return Missing();}component main=Parent();",
    );
    let connected = connected
        .replace("component c=Convert(1);", "var ignored=Broken();component c=Convert(1);");
    assert!(inspect_with(&connected, None, Curve::Goldilocks, 1, QueryForm::Handles).is_none());
}

#[test]
fn generated_input_seeds_and_witness_values_have_distinct_provenance() {
    for (parent, child, expected) in [
        ("signal input x;x===7;component c=Convert(64);c.in<==x;", "", 7),
        ("signal input x;component c=Convert(64);c.in<==x;", "in===7;", 7),
        ("signal x;x<--7;component c=Convert(64);c.in<==x;", "", 0),
    ] {
        let result = inspect(&source(parent, child), None);
        let proof = certificate(result.as_ref());
        assert_eq!(
            proof.input_value(),
            &FieldContext::for_curve(Curve::Goldilocks).canonical(expected.into())
        );
        for (key, first) in proof.assignments()[0].caller() {
            assert_eq!(proof.assignments()[1].caller().get(key), Some(first));
        }
    }
    assert_eq!(
        inspect(&source("component c=Convert(64);c.in<==0;", "in===7;"), None),
        Some(ComponentBitAmbiguityOutcome::NoCertificate(
            NoBitAmbiguityCertificate::CandidatesRejected
        ))
    );
}

#[test]
fn all_parent_and_child_restrictive_equations_survive_source_site_collection() {
    for (parent, child) in [
        ("component c=Convert(64);c.in<==0;c.bits[0]===0;", ""),
        ("component c=Convert(64);c.in<==0;if(1){c.bits[0]===0;}", ""),
        ("component c=Convert(64);c.in<==0;", "bits[0]===0;"),
        ("signal input x;x===0;component c=Convert(64);c.in<==x;c.bits[0]===x;", ""),
    ] {
        assert_eq!(
            inspect(&source(parent, child), None),
            Some(ComponentBitAmbiguityOutcome::NoCertificate(
                NoBitAmbiguityCertificate::CandidatesRejected
            )),
            "{parent} / {child}"
        );
    }
    let result =
        inspect(&source("component c=Convert(64);c.in<==0;if(0){c.bits[0]===0;}", ""), None);
    verify_pair(certificate(result.as_ref()), 0);
}

#[test]
fn checked_requests_reject_foreign_context_curve_project_and_input_bits() {
    let text = source_width(1, "component c=Convert(1);c.in<==0;", "in*(in-1)===0;");
    let project = fixture(&text);
    let provider = ProjectAnalysis::build(&project, Curve::Goldilocks).unwrap();
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main_call) =
        provider.graph().reachable_main_call(main.id(), &project.hir)
    else {
        panic!("main call")
    };
    let caller = provider.contexts().main_evidence(&main_call).unwrap();
    let parent = project.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&project.hir, parent).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("child call")
    };
    let callee = provider.contexts().call_evidence(&call, &facts, &caller).unwrap();
    let cfg = build_cfg(&project.hir, call.callee()).unwrap();
    let child = provider.contexts().analyze_for_evidence(&cfg, &callee, None).unwrap();
    let input_port = project.hir.ports()[0].id;
    let output_port = project.hir.ports()[1].id;
    let input = child.port_handle(input_port, &[]).unwrap();
    let bit = child.port_handle(output_port, &[0]).unwrap();
    let applied = provider.components().apply_component_local_output(&facts, &caller, &call, &bit);
    let applied = applied.certified().unwrap();
    let valid = provider.components().component_bit_ambiguity_handles(
        &facts,
        applied,
        &input,
        std::slice::from_ref(&bit),
    );
    assert_eq!(
        valid.certified(),
        Some(&ComponentBitAmbiguityOutcome::NoCertificate(
            NoBitAmbiguityCertificate::WidthBelowFieldModulus
        ))
    );
    assert_eq!(
        provider
            .components()
            .component_bit_ambiguity_ports(&facts, applied, input_port, output_port)
            .certified(),
        valid.certified()
    );
    assert!(provider
        .components()
        .component_bit_ambiguity_ports(&facts, applied, output_port, input_port)
        .unavailable()
        .is_some());
    assert!(provider
        .components()
        .component_bit_ambiguity_handles(&facts, applied, &bit, std::slice::from_ref(&input))
        .unavailable()
        .is_some());
    let symbolic = provider.contexts().symbolic_root(parent).unwrap();
    let cfg = build_cfg(&project.hir, parent).unwrap();
    let wrong = provider.contexts().analyze_for_evidence(&cfg, &symbolic, None).unwrap();
    assert!(provider
        .components()
        .component_bit_ambiguity_handles(&wrong, applied, &input, std::slice::from_ref(&bit))
        .unavailable()
        .is_some());
    assert!(provider
        .components()
        .component_bit_ambiguity_ports(&wrong, applied, input_port, output_port)
        .unavailable()
        .is_some());
    for curve in [Curve::Bn254, Curve::Goldilocks] {
        let foreign = fixture(&text);
        let other = ProjectAnalysis::build(&foreign, curve).unwrap();
        let definition = foreign.hir.definition("Convert").unwrap();
        let evidence = other.contexts().symbolic_root(definition).unwrap();
        let cfg = build_cfg(&foreign.hir, definition).unwrap();
        let foreign_facts = other.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
        assert!(provider
            .components()
            .component_bit_ambiguity_ports(&foreign_facts, applied, input_port, output_port)
            .unavailable()
            .is_some());
        let scalar = foreign_facts.port_handle(foreign.hir.ports()[0].id, &[]).unwrap();
        assert!(provider
            .components()
            .component_bit_ambiguity_handles(&facts, applied, &scalar, std::slice::from_ref(&bit))
            .unavailable()
            .is_some());
    }
    let other = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    assert!(other
        .components()
        .component_bit_ambiguity_ports(&facts, applied, input_port, output_port)
        .unavailable()
        .is_some());
    assert!(other
        .components()
        .component_bit_ambiguity_handles(&facts, applied, &input, &[bit])
        .unavailable()
        .is_some());
}

#[test]
fn source_output_bounds_and_binding_readiness_remain_required() {
    for parent in [
        "component c=Convert(64);c.in<==0;c.bits[64]===0;",
        "component c=Convert(64);c.in<==0;c.bits[-1]===0;",
        "signal input i;component c=Convert(64);c.in<==0;c.bits[i]===0;",
        "signal x;component c=Convert(64);c.in<==x;x<--0;",
        "signal input i;signal x;if(i){x<--0;}component c=Convert(64);c.in<==x;",
        "component c=Convert(64);signal y;y<--c.bits[0];c.in<==0;",
    ] {
        assert!(inspect(&source(parent, ""), None).is_none(), "{parent}");
    }
}

#[test]
fn closure_preserves_additional_bound_and_external_inputs() {
    for (parent, child) in [
        ("signal input x;signal input z;z===7;component c=Convert(64);c.in<==x;", ""),
        ("component c=Convert(64);c.in<==0;c.aux<==7;", "signal input aux;aux===7;"),
    ] {
        let result = inspect(&source(parent, child), None);
        let proof = certificate(result.as_ref());
        assert_eq!(proof.assignments()[0].caller(), proof.assignments()[1].caller());
        let seven = FieldContext::for_curve(Curve::Goldilocks).canonical(7.into());
        assert!(proof.assignments()[0].caller().values().any(|value| value == &seven));
        for (key, value) in proof.assignments()[0].callee() {
            if value == &seven {
                assert_eq!(proof.assignments()[1].callee().get(key), Some(value));
            }
        }
    }
    assert!(inspect(&source("component c=Convert(64);c.in<==0;", "assert(in==0);"), None).is_none());
}

#[test]
fn bn254_canonical_loop_closure_obeys_the_actual_field_boundary() {
    for width in [253, 254] {
        let source = format!(
            "template Convert(n){{signal input in;signal output bits[n];var sum=0;\
            for(var i=0;i<n;i++){{bits[i]<--(in >> i)&1;bits[i]*(bits[i]-1)===0;\
            sum+=bits[i]*(2**i);}}in===sum;}}\
            template Parent(){{signal input x;component c=Convert({width});c.in<==x;}}\
            component main=Parent();"
        );
        let result = inspect_with(&source, None, Curve::Bn254, width, QueryForm::Handles);
        if width == 253 {
            assert_eq!(
                result,
                Some(ComponentBitAmbiguityOutcome::NoCertificate(
                    NoBitAmbiguityCertificate::WidthBelowFieldModulus
                ))
            );
        } else {
            let proof = certificate(result.as_ref());
            assert_eq!(proof.decomposition().curve(), &Curve::Bn254);
            assert_ne!(proof.representations()[0], proof.representations()[1]);
            let field = FieldContext::for_curve(Curve::Bn254);
            for representation in proof.representations() {
                let integer =
                    BigInt::parse_bytes(representation.integer().to_string().as_bytes(), 10)
                        .unwrap();
                assert_eq!(field.canonical(integer), *proof.input_value());
            }
            assert_eq!(proof.assignments()[0].caller(), proof.assignments()[1].caller());
            assert_eq!(proof.callee_constraint_origins().len(), width + 1);
        }
    }
}

#[test]
fn main_output_forwarding_completes_both_parent_models() {
    let source = source("component c=Convert(64);c.in<==0;signal output out;out<==c.bits[0];", "");
    let result = inspect(&source, None);
    let proof = certificate(result.as_ref());
    let field = FieldContext::for_curve(Curve::Goldilocks);
    let one = field.canonical(1.into());
    assert!(proof.assignments()[0].caller().values().all(|value| field.is_zero(value)));
    assert_eq!(proof.assignments()[1].caller().values().filter(|value| *value == &one).count(), 2);
    assert_eq!(proof.caller_constraint_origins().len(), 2);
}

#[test]
fn generated_output_chains_preserve_external_inputs_and_all_restrictions() {
    let prefix = "signal input z;z===7;component c=Convert(64);c.in<==0;\
        signal output out;signal mid;mid<==c.bits[0]+z;out<==mid*2;";
    let source = source(prefix, "");
    let result = inspect(&source, None);
    let proof = certificate(result.as_ref());
    let field = FieldContext::for_curve(Curve::Goldilocks);
    for (index, assignment) in proof.assignments().iter().enumerate() {
        assert!(assignment.caller().values().any(|value| value == &field.canonical(7.into())));
        let output = field.canonical((14 + 2 * index).into());
        assert!(assignment.caller().values().any(|value| value == &output));
    }
    assert_eq!(proof.caller_constraint_origins().len(), 4);
    let restricted = source.replace("out<==mid*2;", "out<==mid*2;out===14;");
    assert_eq!(
        inspect(&restricted, None),
        Some(ComponentBitAmbiguityOutcome::NoCertificate(
            NoBitAmbiguityCertificate::CandidatesRejected,
        ))
    );
}

#[test]
fn forwarding_completion_never_changes_external_inputs_or_witness_assignments() {
    for parent in [
        "signal input out;component c=Convert(64);c.in<==0;out===c.bits[0];",
        "component c=Convert(64);c.in<==0;signal output out;out<--c.bits[0];out===c.bits[0];",
    ] {
        let result = inspect(&source(parent, ""), None);
        assert_eq!(
            result,
            Some(ComponentBitAmbiguityOutcome::NoCertificate(
                NoBitAmbiguityCertificate::CandidatesRejected,
            ))
        );
    }
}

#[test]
fn generated_parent_signal_completion_sets_child_input_before_pair_selection() {
    let result = inspect(
        &source(
            "signal input z;signal value;value<==z+1;\
        component c=Convert(64);c.in<==value;signal output out;out<==c.bits[0];",
            "",
        ),
        None,
    );
    let proof = certificate(result.as_ref());
    let field = FieldContext::for_curve(Curve::Goldilocks);
    assert_eq!(proof.input_value(), &field.canonical(1.into()));
    assert!(proof
        .assignments()
        .iter()
        .all(|model| { model.caller().values().any(|value| value == &field.canonical(0.into())) }));
}

#[test]
fn temporary_component_views_preserve_ambiguity_outcomes() {
    let text = source_width(1, "component c=Convert(1);c.in<==0;", "in*(in-1)===0;");
    let project = fixture(&text);
    let provider = ProjectAnalysis::build(&project, Curve::Goldilocks).unwrap();
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main_call) =
        provider.graph().reachable_main_call(main.id(), &project.hir)
    else {
        panic!("main call")
    };
    let caller = provider.contexts().main_evidence(&main_call).unwrap();
    let parent = project.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&project.hir, parent).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("child call")
    };
    let callee = provider.contexts().call_evidence(&call, &facts, &caller).unwrap();
    let cfg = build_cfg(&project.hir, call.callee()).unwrap();
    let child = provider.contexts().analyze_for_evidence(&cfg, &callee, None).unwrap();
    let input_port = project.hir.ports()[0].id;
    let output_port = project.hir.ports()[1].id;
    let input = child.port_handle(input_port, &[]).unwrap();
    let bit = child.port_handle(output_port, &[0]).unwrap();
    let applied = provider.components().apply_component_local_output(&facts, &caller, &call, &bit);
    let applied = applied.certified().unwrap();
    let first = provider.components().component_bit_ambiguity_handles(
        &facts,
        applied,
        &input,
        std::slice::from_ref(&bit),
    );
    let second = {
        let queries = provider.components();
        queries.component_bit_ambiguity_handles(&facts, applied, &input, std::slice::from_ref(&bit))
    };
    assert_eq!(first, second);
    assert_eq!(
        first.certified(),
        Some(&ComponentBitAmbiguityOutcome::NoCertificate(
            NoBitAmbiguityCertificate::WidthBelowFieldModulus
        ))
    );
}
