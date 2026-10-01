use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::{analyze, AccessHandleError, FactBlocker, FieldContext};
use parser::hir::{lower_project, DefinitionRef, HirProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;
use std::fs;

fn project(source: &str) -> HirProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-output-handles-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let file = directory.join("case.circom");
    fs::write(&file, source).unwrap();
    let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lowered = lower_project(&loaded);
    assert!(lowered.syntax_diagnostics.is_empty(), "{:?}", lowered.syntax_diagnostics);
    assert!(lowered.diagnostics.is_empty(), "{:?}", lowered.diagnostics);
    lowered.hir
}

#[test]
fn declared_port_without_source_access_has_a_queryable_handle() {
    let hir = project("template Check(){signal input unused; signal output y; y <== 1;}");
    let definition = hir.definition("Check").unwrap();
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let DefinitionRef::Template(id) = definition else { panic!("expected template") };
    let port = hir.template(id).unwrap().ports[0];
    let handle = facts.port_handle(port, &[]).unwrap();
    assert_eq!(facts.read_handle(&handle).certified(), Some(&false));
}

#[test]
fn declared_port_handle_distinguishes_a_read_from_an_unused_port() {
    let hir = project(
        "template Check(){signal input used; signal input unused; signal output y; y <== used;}",
    );
    let definition = hir.definition("Check").unwrap();
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let DefinitionRef::Template(id) = definition else { panic!("expected template") };
    let ports = &hir.template(id).unwrap().ports;
    let used = facts.port_handle(ports[0], &[]).unwrap();
    let unused = facts.port_handle(ports[1], &[]).unwrap();
    assert_eq!(facts.read_handle(&used).certified(), Some(&true));
    assert_eq!(facts.read_handle(&unused).certified(), Some(&false));
}

#[test]
fn unreferenced_component_output_has_schema_but_no_local_read_certificate() {
    let hir = project(concat!(
        "template Child(){signal output out; out <== 1;} ",
        "template Check(){component c=Child();}"
    ));
    let definition = hir.definition("Check").unwrap();
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let child = hir.definition("Child").unwrap();
    let DefinitionRef::Template(child) = child else { panic!("expected template") };
    let output = hir.template(child).unwrap().ports[0];
    let component = hir.components()[0].id;
    let handle = facts.component_output_handle(component, &[], output, &[]).unwrap();
    assert_eq!(handle.component(), Some(component));
    assert!(facts
        .read_handle(&handle)
        .unavailable()
        .unwrap()
        .contains(&FactBlocker::ExternalSummary));
}

#[test]
fn output_handle_rejects_grafted_ports_and_foreign_owners() {
    let hir = project(concat!(
        "template Child(){signal output out;} template Other(){signal output other;} ",
        "template Check(){component c=Child();} template Else(){signal output y;}"
    ));
    let field = FieldContext::for_curve(Curve::Bn254);
    let check = hir.definition("Check").unwrap();
    let cfg = build_cfg(&hir, check).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let DefinitionRef::Template(other) = hir.definition("Other").unwrap() else {
        panic!("expected template")
    };
    let wrong = hir.template(other).unwrap().ports[0];
    let component = hir.components()[0].id;
    assert_eq!(
        facts.component_output_handle(component, &[], wrong, &[]).unwrap_err(),
        AccessHandleError::PortNotInTemplate
    );
    let else_cfg = build_cfg(&hir, hir.definition("Else").unwrap()).unwrap();
    let else_facts = analyze(&hir, &else_cfg, &field, None).unwrap();
    assert_eq!(
        else_facts.component_output_handle(component, &[], wrong, &[]).unwrap_err(),
        AccessHandleError::ForeignComponent
    );
}

#[test]
fn component_array_handle_requires_an_in_bounds_exact_index() {
    let hir = project(concat!(
        "template Child(){signal output out;} ",
        "template Check(){component c[2]; c[0]=Child(); c[1]=Child();}"
    ));
    let definition = hir.definition("Check").unwrap();
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let DefinitionRef::Template(child) = hir.definition("Child").unwrap() else {
        panic!("expected template")
    };
    let output = hir.template(child).unwrap().ports[0];
    let component = hir.components()[0].id;
    assert!(facts.component_output_handle(component, &[0], output, &[]).is_ok());
    assert!(facts.component_output_handle(component, &[1], output, &[]).is_ok());
    assert_eq!(
        facts.component_output_handle(component, &[2], output, &[]).unwrap_err(),
        AccessHandleError::IndexOutOfBounds
    );
}

#[test]
fn component_array_handle_does_not_graft_another_elements_instantiation() {
    let hir = project(concat!(
        "template Child(){signal output out;} ",
        "template Check(){component c[2]; c[1]=Child();}"
    ));
    let definition = hir.definition("Check").unwrap();
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let DefinitionRef::Template(child) = hir.definition("Child").unwrap() else {
        panic!("expected template")
    };
    let output = hir.template(child).unwrap().ports[0];
    let component = hir.components()[0].id;
    assert_eq!(
        facts.component_output_handle(component, &[0], output, &[]).unwrap_err(),
        AccessHandleError::NoInstantiation
    );
    assert!(facts.component_output_handle(component, &[1], output, &[]).is_ok());
}

#[test]
fn handles_cannot_cross_project_definition_or_curve() {
    let source = "template Check(){signal input x;} template Else(){signal input x;}";
    let hir = project(source);
    let definition = hir.definition("Check").unwrap();
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let DefinitionRef::Template(id) = definition else { panic!("expected template") };
    let handle = facts.port_handle(hir.template(id).unwrap().ports[0], &[]).unwrap();
    let other = project(source);
    let other_cfg = build_cfg(&other, other.definition("Check").unwrap()).unwrap();
    let other_facts = analyze(&other, &other_cfg, &field, None).unwrap();
    assert!(other_facts
        .read_handle(&handle)
        .unavailable()
        .unwrap()
        .contains(&FactBlocker::ForeignDefinition));
    let else_cfg = build_cfg(&hir, hir.definition("Else").unwrap()).unwrap();
    let else_facts = analyze(&hir, &else_cfg, &field, None).unwrap();
    assert!(else_facts
        .read_handle(&handle)
        .unavailable()
        .unwrap()
        .contains(&FactBlocker::ForeignDefinition));
    let goldilocks = FieldContext::for_curve(Curve::Goldilocks);
    let curve_facts = analyze(&hir, &cfg, &goldilocks, None).unwrap();
    assert!(curve_facts
        .read_handle(&handle)
        .unavailable()
        .unwrap()
        .contains(&FactBlocker::ForeignQuery));
}

#[test]
fn bus_output_port_has_a_schema_backed_handle() {
    let hir = project(concat!(
        "bus B(){signal leaf;} template Child(){B output out;} ",
        "template Check(){component c=Child();}"
    ));
    let definition = hir.definition("Check").unwrap();
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let DefinitionRef::Template(child) = hir.definition("Child").unwrap() else {
        panic!("expected template")
    };
    let output = hir.template(child).unwrap().ports[0];
    let handle = facts.component_output_handle(hir.components()[0].id, &[], output, &[]).unwrap();
    assert_eq!(handle.component(), Some(hir.components()[0].id));
    assert!(facts
        .read_handle(&handle)
        .unavailable()
        .unwrap()
        .contains(&FactBlocker::ExternalSummary));
}

#[test]
fn component_handle_rejects_an_input_port() {
    let hir = project(concat!(
        "template Child(){signal input in; signal output out;} ",
        "template Check(){component c=Child();}"
    ));
    let definition = hir.definition("Check").unwrap();
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let DefinitionRef::Template(child) = hir.definition("Child").unwrap() else {
        panic!("expected template")
    };
    let input = hir.template(child).unwrap().ports[0];
    assert_eq!(
        facts.component_output_handle(hir.components()[0].id, &[], input, &[]).unwrap_err(),
        AccessHandleError::NotOutput
    );
}

#[test]
fn parameter_dependent_output_shape_has_no_exact_handle_without_specialization() {
    let hir = project(concat!(
        "template Child(n){signal output out[n];} ",
        "template Check(n){component c=Child(n);}"
    ));
    let definition = hir.definition("Check").unwrap();
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let DefinitionRef::Template(child) = hir.definition("Child").unwrap() else {
        panic!("expected template")
    };
    let output = hir.template(child).unwrap().ports[0];
    assert_eq!(
        facts.component_output_handle(hir.components()[0].id, &[], output, &[0]).unwrap_err(),
        AccessHandleError::UnprovedShape
    );
}
