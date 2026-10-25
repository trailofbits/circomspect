// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::assert_is_empty,
    clippy::expect_used,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use std::fs;

use circomspect_program_analysis::hir_facts::{FieldContext, Incidence};
use circomspect_program_analysis::interprocedural::{ArgumentValue, ProjectSummaries};
use parser::hir::{lift_project, DefinitionRef, LiftedProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-template-validity-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

#[test]
fn definitely_invalid_templates_cannot_certify_ports_reads_or_witnesses() {
    for statement in [
        "var x[-1];",
        "var x[2][-1];",
        "var x[18446744073709551616];",
        "assert(0);",
        "var x=1/0;",
        "var x=1\\0;",
        "var x=1%0;",
        "var x=1;x/=0;",
        "var x=1;x\\=0;",
        "var x=1;x%=0;",
        "var x[1];x[1]=2;",
        "var x[1];var t=x[1];",
    ] {
        let lifted = fixture(&format!("template T(){{{statement}signal output y;y<==1;}}"));
        assert!(lifted.diagnostics.is_empty(), "{statement}: {:?}", lifted.diagnostics);
        assert!(lifted.syntax_diagnostics.is_empty());
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("T").unwrap();
        let DefinitionRef::Template(template) = definition else { panic!("template T") };
        let context = provider.symbolic_context_for(definition).unwrap();
        let output = lifted.hir.template(template).unwrap().ports[0];
        let port = provider.template_port(template, &context, output);
        assert!(port.certified().is_none(), "{statement}: {port:?}");
        assert!(provider.template_port_read(template, &context, output).certified().is_none());
        assert!(provider.template_port_witnesses(template, &context, output).certified().is_none());
    }
}

#[test]
fn invalid_bus_field_dimensions_block_unrelated_port_certificates() {
    for bus in ["bus B(){signal x[-1];}", "bus Inner(){signal x[-1];} bus B(){Inner() inner;}"] {
        for declaration in ["B() b;", "B() b[0];", "B() b[1];"] {
            let lifted =
                fixture(&format!("{bus} template T(){{{declaration}signal output y;y<==1;}}"));
            assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
            let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
            let definition = lifted.hir.definition("T").unwrap();
            let DefinitionRef::Template(template) = definition else { panic!("template T") };
            let context = provider.symbolic_context_for(definition).unwrap();
            let output = lifted.hir.template(template).unwrap().ports[0];
            assert!(provider.template_port(template, &context, output).certified().is_none());
        }
    }
}

#[test]
fn an_unused_invalid_bus_definition_preserves_independent_template_facts() {
    let lifted = fixture("bus B(){signal x[-1];} template T(){signal output y;y<==1;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let DefinitionRef::Template(template) = definition else { panic!("template T") };
    let context = provider.symbolic_context_for(definition).unwrap();
    let output = lifted.hir.template(template).unwrap().ports[0];
    let facts = provider.template_port(template, &context, output);
    assert_eq!(facts.certified().unwrap().incidence(), Incidence::Must);
}

#[test]
fn custom_and_external_templates_never_supply_trusted_port_effects() {
    for modifier in ["custom", "extern_c"] {
        let lifted = fixture(&format!(
            "pragma custom_templates; template {modifier} T(){{signal output y;y<==1;}}"
        ));
        assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("T").unwrap();
        let DefinitionRef::Template(template) = definition else { panic!("template T") };
        let declaration = lifted.hir.template(template).unwrap();
        assert!(declaration.custom || declaration.external);
        let context = provider.symbolic_context_for(definition).unwrap();
        let output = declaration.ports[0];
        assert!(provider.template_port(template, &context, output).certified().is_none());
        assert!(provider.template_port_read(template, &context, output).certified().is_none());
        assert!(provider.template_port_witnesses(template, &context, output).certified().is_none());
    }
}

#[test]
fn literal_dimensions_use_canonical_field_values() {
    for curve in [Curve::Bn254, Curve::Bls12_381, Curve::Goldilocks] {
        let field = FieldContext::for_curve(curve.clone());
        let negative = field.canonical((-1).into());
        let modulus = negative.as_bigint() + 1_u32;
        for (size, invalid) in
            [(negative.as_bigint().to_string(), true), (modulus.to_string(), false)]
        {
            let lifted = fixture(&format!("template T(){{var x[{size}];signal output y;y<==1;}}"));
            let provider = ProjectSummaries::build(&lifted, curve.clone()).unwrap();
            let definition = lifted.hir.definition("T").unwrap();
            let DefinitionRef::Template(template) = definition else { panic!("template T") };
            let context = provider.symbolic_context_for(definition).unwrap();
            let output = lifted.hir.template(template).unwrap().ports[0];
            let result = provider.template_port(template, &context, output);
            assert_eq!(result.certified().is_none(), invalid, "{size}: {result:?}");
        }
    }
}

#[test]
fn declaration_validity_uses_the_selected_curve_and_parameter_context() {
    let lifted = fixture("template T(n){var x[n];signal output y;y<==1;}");
    let definition = lifted.hir.definition("T").unwrap();
    let DefinitionRef::Template(template) = definition else { panic!("template T") };
    let output = lifted.hir.template(template).unwrap().ports[0];
    for curve in [Curve::Bn254, Curve::Bls12_381, Curve::Goldilocks] {
        let provider = ProjectSummaries::build(&lifted, curve.clone()).unwrap();
        let field = FieldContext::for_curve(curve);
        for size in [-1, 0, 1, 2] {
            let context = provider
                .context_for(definition, vec![ArgumentValue::Scalar(field.canonical(size.into()))])
                .unwrap();
            let port = provider.template_port(template, &context, output);
            if size < 0 {
                assert!(port.certified().is_none(), "{port:?}");
            } else {
                assert_eq!(port.certified().unwrap().incidence(), Incidence::Must);
                assert_eq!(
                    port.certified().unwrap().fixed_value(),
                    Some(&field.canonical(1.into()))
                );
            }
        }
    }
}

#[test]
fn valid_execution_and_unrelated_opacity_preserve_independent_port_facts() {
    for statement in [
        "var x[0];",
        "assert(1);",
        "var x=1/1;",
        "var x[1];x[0]=2;",
        "if(0){assert(0);}",
        "var x=Missing();",
    ] {
        let lifted = fixture(&format!("template T(){{{statement}signal output y;y<==1;}}"));
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("T").unwrap();
        let DefinitionRef::Template(template) = definition else { panic!("template T") };
        let context = provider.symbolic_context_for(definition).unwrap();
        let output = lifted.hir.template(template).unwrap().ports[0];
        let port = provider.template_port(template, &context, output);
        assert_eq!(
            port.certified()
                .map(circomspect_program_analysis::interprocedural::PortSummary::incidence),
            Some(Incidence::Must),
            "{statement}: {port:?}"
        );
    }
}

#[test]
fn unproved_access_bounds_do_not_invalidate_independent_port_facts() {
    for (index, available) in [("n", true), ("0", true), ("1", false)] {
        let source = format!(
            "template T(n){{var values[1]=[2];var value=values[{index}];signal output y;y<==1;}}"
        );
        let lifted = fixture(&source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("T").unwrap();
        let DefinitionRef::Template(template) = definition else { panic!("template T") };
        let context = provider.symbolic_context_for(definition).unwrap();
        let output = lifted.hir.template(template).unwrap().ports[0];
        let summary = provider.template_port(template, &context, output);
        assert_eq!(
            summary
                .certified()
                .map(circomspect_program_analysis::interprocedural::PortSummary::incidence),
            if available { Some(Incidence::Must) } else { None },
            "index {index}: {summary:?}"
        );
    }
}
