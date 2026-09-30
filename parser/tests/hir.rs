use circomspect_parser::hir::{
    lower_project, AccessStep, BusTarget, CallTarget, DefinitionRef, Effect, ExprKind,
    IncompleteReason, Knownness, SemanticCode, Severity,
};
use circomspect_parser::new_frontend::{load_sources, Version, VersionPolicy};
use std::fs;
use std::path::PathBuf;

fn lower(sources: &[(&str, &str)], version: Version) -> circomspect_parser::hir::LoweredProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-hir-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).expect("test fixture directory");
    let mut roots = Vec::new();
    for (name, text) in sources {
        let path = directory.join(name);
        fs::write(&path, text).expect("test fixture");
        roots.push(path);
    }
    let project = load_sources(&roots, &[PathBuf::from(&directory)], VersionPolicy::new(version));
    lower_project(&project)
}

fn effect_for<'a>(result: &'a circomspect_parser::hir::LoweredProject, name: &str) -> &'a [Effect] {
    let definition = result.hir.templates().iter().find(|item| item.name == name).unwrap();
    &result.hir.block(definition.body).unwrap().effects
}

#[test]
fn whole_project_resolution_keeps_independent_definitions() {
    let result = lower(
        &[
            ("a.circom", "function F() { return G(); } function Good() { return 1; }"),
            ("b.circom", "function G() { return 2; }"),
        ],
        Version::new(2, 2, 3),
    );
    assert_eq!(result.hir.functions().len(), 3);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(result.incomplete.is_empty(), "{:?}", result.incomplete);
    assert!(result.hir.functions().iter().any(|function| function.name == "Good"));
}

#[test]
fn duplicate_global_names_are_ambiguous() {
    let result = lower(
        &[
            ("a.circom", "function F() { return 1; } function Use() { return F(); }"),
            ("b.circom", "template F() {}"),
        ],
        Version::new(2, 2, 3),
    );
    assert_eq!(result.diagnostics.len(), 2);
    assert!(result.diagnostics.iter().all(|diagnostic| {
        diagnostic.code == SemanticCode::DuplicateSymbol && diagnostic.severity == Severity::Error
    }));
    let use_function =
        result.hir.functions().iter().find(|function| function.name == "Use").unwrap();
    let body = result.hir.block(use_function.body).unwrap();
    let call = result.hir.expression(body.expressions()[0]).unwrap();
    assert!(matches!(call.call_target(), Some(CallTarget::Ambiguous { .. })));
    assert!(result.hir.definition("F").is_none());
    assert_eq!(result.hir.definitions_named("F").len(), 2);
    assert!(result
        .hir
        .definitions_named("F")
        .contains(&DefinitionRef::Function(result.hir.functions()[0].id)));
}

#[test]
fn forward_ports_resolve_but_internal_signals_do_not() {
    let result = lower(
        &[("main.circom", "template Use() { component c = Later(); signal output out; out <== c.visible; out <== c.hidden; } template Later() { signal output visible; signal hidden; }")],
        Version::new(2, 2, 3),
    );
    assert!(result.hir.expressions().iter().any(|expression| {
        matches!(&expression.kind, ExprKind::Access(path) if path.steps.iter().any(|step| matches!(step, AccessStep::Port { .. })))
    }));
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|item| item.code == SemanticCode::InvalidSignalAccess)
            .count(),
        1
    );
    assert!(result
        .hir
        .expressions()
        .iter()
        .any(|expression| { matches!(expression.kind, ExprKind::Opaque(_)) }));
}

#[test]
fn for_initializer_is_visible_inside_loop_only() {
    let result = lower(
        &[(
            "loop.circom",
            "function F() { var x = 0; for (var i = 0; i < 2; i++) { x += i; } return x; }",
        )],
        Version::new(2, 2, 3),
    );
    assert!(result.syntax_diagnostics.is_empty(), "{:?}", result.syntax_diagnostics);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(effect_for_function(&result, "F")
        .iter()
        .any(|effect| matches!(effect, Effect::For { .. })));
}

fn effect_for_function<'a>(
    result: &'a circomspect_parser::hir::LoweredProject,
    name: &str,
) -> &'a [Effect] {
    let definition = result.hir.functions().iter().find(|item| item.name == name).unwrap();
    &result.hir.block(definition.body).unwrap().effects
}

#[test]
fn named_anonymous_inputs_keep_checked_destination_and_operator() {
    let result = lower(
        &[("anonymous.circom", "template Child() { signal input in; signal output out; out <== in; } template Use() { signal output out; out <== Child()(in <== 1); }")],
        Version::new(2, 2, 3),
    );
    assert!(result.syntax_diagnostics.is_empty(), "{:?}", result.syntax_diagnostics);
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(effect_for(&result, "Use")
        .iter()
        .any(|effect| matches!(effect, Effect::ConstraintAssignment { .. })));
    let anonymous = result
        .hir
        .expressions()
        .iter()
        .find(|expr| matches!(expr.kind, ExprKind::AnonymousComponent { .. }))
        .unwrap();
    let ExprKind::AnonymousComponent { inputs, .. } = &anonymous.kind else { unreachable!() };
    assert_eq!(inputs.len(), 1);
    assert!(inputs[0].resolved_port().is_some());
    assert_eq!(inputs[0].operator().as_str(), "<==");
}

#[test]
fn named_anonymous_input_near_misses_are_located() {
    let result = lower(
        &[("anonymous.circom", "template Child() { signal input in; } template Use() { signal output out; out <== Child()(nope <== 1); out <== Child()(in <-- 1); }")],
        Version::new(2, 2, 3),
    );
    assert_eq!(
        result.diagnostics.iter().filter(|item| item.code == SemanticCode::AnonymousInput).count(),
        2
    );
    assert!(result.incomplete.len() >= 2);
}

#[test]
fn declaration_initializers_keep_witness_and_constraint_effects_distinct() {
    let result = lower(
        &[(
            "effects.circom",
            "template T() { signal input x; signal output a <-- x; signal output b <== x; }",
        )],
        Version::new(2, 2, 3),
    );
    assert!(result.syntax_diagnostics.is_empty(), "{:?}", result.syntax_diagnostics);
    let effects = effect_for(&result, "T");
    assert_eq!(
        effects.iter().filter(|effect| matches!(effect, Effect::WitnessAssignment { .. })).count(),
        1
    );
    assert_eq!(
        effects
            .iter()
            .filter(|effect| matches!(effect, Effect::ConstraintAssignment { .. }))
            .count(),
        1
    );
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
}

#[test]
fn witness_dependent_variable_cannot_certify_array_length() {
    let source = "template T() { signal input x; var n = x; signal a[n]; }";
    let result = lower(&[("knownness.circom", source)], Version::new(2, 2, 3));
    let diagnostic = result
        .diagnostics
        .iter()
        .find(|item| item.code == SemanticCode::NonConstantArrayLength)
        .unwrap();
    assert_eq!(diagnostic.severity, Severity::Error);
    assert_eq!(&source[diagnostic.span.start()..diagnostic.span.end()], "n");
    assert!(result.incomplete.iter().any(|item| item.reason == IncompleteReason::NonCompileTime));

    let valid = lower(
        &[("constant.circom", "template T() { var n = 2; signal a[n]; }")],
        Version::new(2, 2, 3),
    );
    assert!(valid.diagnostics.is_empty(), "{:?}", valid.diagnostics);
}

#[test]
fn bus_inline_array_version_check_resolves_through_include() {
    let root = "include \"bus.circom\"; template T() { B b; var a = [b]; }";
    let sources = &[("root.circom", root), ("bus.circom", "bus B() { signal x; }")];
    let old = lower(sources, Version::new(2, 2, 2));
    let version_errors: Vec<_> =
        old.diagnostics.iter().filter(|item| item.code == SemanticCode::FeatureVersion).collect();
    assert_eq!(version_errors.len(), 1, "{:?}", old.diagnostics);
    assert_eq!(version_errors[0].severity, Severity::Error);
    assert_eq!(&root[version_errors[0].span.start()..version_errors[0].span.end()], "[b]");
    let current = lower(sources, Version::new(2, 2, 3));
    assert!(current.diagnostics.is_empty(), "{:?}", current.diagnostics);

    let ordinary =
        lower(&[("plain.circom", "template T(){var a = [1,2];}")], Version::new(2, 2, 2));
    assert!(ordinary.diagnostics.is_empty(), "{:?}", ordinary.diagnostics);
}

#[test]
fn bus_type_errors_distinguish_missing_and_wrong_kind() {
    let source = "function F() { return 1; } template T() { F a; Missing b; }";
    let result = lower(&[("bus.circom", source)], Version::new(2, 2, 3));
    let errors: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|item| item.code == SemanticCode::MissingBusType)
        .collect();
    assert_eq!(errors.len(), 2, "{:?}", result.diagnostics);
    assert!(matches!(
        result.hir.symbols().iter().find(|item| item.name == "a").unwrap().bus_type,
        Some(BusTarget::WrongKind { .. })
    ));
    assert!(matches!(
        result.hir.symbols().iter().find(|item| item.name == "b").unwrap().bus_type,
        Some(BusTarget::Missing { .. })
    ));
    assert_eq!(errors[0].actual_kind, Some(circomspect_parser::hir::DefinitionKind::Function));
    assert_eq!(errors[1].actual_kind, None);
    assert!(errors[0].message.contains("function") || errors[0].message.contains("Function"));
    assert!(errors[1].message.contains("unknown"));
    assert_eq!(&source[errors[0].span.start()..errors[0].span.end()], "F");
    assert_eq!(&source[errors[1].span.start()..errors[1].span.end()], "Missing");
}

#[test]
fn component_input_assignment_targets_port_and_output_is_rejected() {
    let source = "template Child(){signal input in; signal output out;} template Use(){signal input x; component c = Child(); c.in <== x; c.out <== x;}";
    let result = lower(&[("ports.circom", source)], Version::new(2, 2, 3));
    let effects = effect_for(&result, "Use");
    assert!(effects.iter().any(|effect| matches!(effect, Effect::ConstraintAssignment { target, .. } if matches!(target.steps.last(), Some(AccessStep::Port { .. })))));
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|item| item.code == SemanticCode::InvalidAssignment)
            .count(),
        1
    );
    assert!(effects.iter().any(|effect| matches!(effect, Effect::Opaque { .. })));
}

#[test]
fn tag_assignment_does_not_turn_signal_into_compile_time_value() {
    let source =
        "template T() { signal input {binary} s; s.binary = 1; var t = s.binary; signal a[s]; }";
    let result = lower(&[("tags.circom", source)], Version::new(2, 2, 3));
    let signal = result.hir.symbols().iter().find(|item| item.name == "s").unwrap();
    assert_eq!(signal.knownness, Knownness::WitnessDependent);
    assert!(result.hir.expressions().iter().any(|expr| matches!(&expr.kind, ExprKind::Access(path) if path.steps.iter().any(|step| matches!(step, AccessStep::Tag { .. })))));
    assert!(result
        .diagnostics
        .iter()
        .any(|item| item.code == SemanticCode::NonConstantArrayLength));
}

#[test]
fn tuple_component_initializers_bind_each_template_call() {
    let source = "template A() {} template B() {} template T() { component (a,b) = (A(),B()); }";
    let result = lower(&[("tuple.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert_eq!(result.hir.components().len(), 2);
    assert!(result
        .hir
        .components()
        .iter()
        .all(|component| matches!(component.target, Some(CallTarget::Template(_)))));
    let invalid = lower(
        &[(
            "bad.circom",
            "template A() {} template B() {} template T() { component (a,b) = (A(),B(),A()); }",
        )],
        Version::new(2, 2, 3),
    );
    assert!(invalid.diagnostics.iter().any(|item| item.code == SemanticCode::InvalidAssignment));
}
