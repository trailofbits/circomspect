use circomspect_parser::hir::{
    lower_project, AccessStep, BusTarget, CallTarget, DefinitionRef, Effect, ExprKind,
    IncompleteLocation, IncompleteReason, Knownness, SemanticCode, Severity,
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
fn local_bus_and_anonymous_array_version_boundaries_are_distinct() {
    let local = "bus B(){signal x;} template T(){B b; var a=[b];}";
    let old = lower(&[("local.circom", local)], Version::new(2, 2, 2));
    assert_eq!(old.diagnostics.len(), 1);
    assert_eq!(old.diagnostics[0].code, SemanticCode::FeatureVersion);
    assert_eq!(&local[old.diagnostics[0].span.start()..old.diagnostics[0].span.end()], "[b]");
    let current = lower(&[("local.circom", local)], Version::new(2, 2, 3));
    assert!(current.diagnostics.is_empty(), "{:?}", current.diagnostics);

    let anonymous = "template Child(){signal input in;} template T(){var a=[Child()(1)];}";
    let old = lower(&[("anonymous_array.circom", anonymous)], Version::new(2, 2, 2));
    assert!(old.syntax_diagnostics.iter().any(|item| {
        item.kind == circomspect_parser::new_frontend::DiagnosticKind::FeatureVersion
            && item
                .span()
                .is_some_and(|span| &anonymous[span.start()..span.end()] == "[Child()(1)]")
    }));
    let current = lower(&[("anonymous_array.circom", anonymous)], Version::new(2, 2, 3));
    assert!(!current.syntax_diagnostics.iter().any(|item| {
        item.kind == circomspect_parser::new_frontend::DiagnosticKind::FeatureVersion
    }));
}

#[test]
fn unresolved_inline_array_element_type_is_incomplete() {
    let source = "template T(v){var a=[v];}";
    let result = lower(&[("unknown_array.circom", source)], Version::new(2, 2, 2));
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(result.incomplete.iter().any(|item| {
        item.reason == IncompleteReason::UnknownType
            && item.span().is_some_and(|span| &source[span.start()..span.end()] == "[v]")
    }));
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

fn diagnostic_fingerprint(
    result: &circomspect_parser::hir::LoweredProject,
) -> Vec<(SemanticCode, Severity, usize, usize, usize)> {
    result
        .diagnostics
        .iter()
        .map(|item| {
            (
                item.code,
                item.severity,
                item.span.source().index(),
                item.span.start(),
                item.span.end(),
            )
        })
        .collect()
}

#[test]
fn missing_targets_have_exact_order_level_and_name_spans() {
    let source = "function F(){return MissingA();} template T(){component c=MissingT(); signal output out; out <== MissingB(MissingC()); out <== MissingAnon()(1);} component main=MissingMain();";
    let result = lower(&[("missing.circom", source)], Version::new(2, 2, 3));
    assert!(result.syntax_diagnostics.is_empty(), "{:?}", result.syntax_diagnostics);
    let expected: Vec<_> =
        ["MissingA", "MissingT", "MissingB", "MissingC", "MissingAnon", "MissingMain"]
            .iter()
            .map(|name| {
                let start = source.find(name).unwrap();
                (SemanticCode::MissingCall, Severity::Error, 0, start, start + name.len())
            })
            .collect();
    assert_eq!(diagnostic_fingerprint(&result), expected);
    assert!(matches!(result.hir.mains[0].target, CallTarget::Missing { .. }));
}

#[test]
fn wrong_kind_targets_have_exact_directional_codes_and_spans() {
    let source = "function F(){return 1;} template T(){} bus B(){signal x;} function Use(){return T()+B();} template Main(){F a; T b; component cf=F(); component cb=B(); signal output out; out <== F()(1);} component main=F();";
    let result = lower(&[("wrong.circom", source)], Version::new(2, 2, 3));
    assert!(result.syntax_diagnostics.is_empty(), "{:?}", result.syntax_diagnostics);
    let at =
        |context: &str, name: &str| source.find(context).unwrap() + context.find(name).unwrap();
    let calls = [
        (at("return T()+B()", "T"), SemanticCode::WrongFunction),
        (at("return T()+B()", "B"), SemanticCode::WrongFunction),
        (at("F a;", "F"), SemanticCode::MissingBusType),
        (at("T b;", "T"), SemanticCode::MissingBusType),
        (at("component cf=F()", "F"), SemanticCode::WrongTemplate),
        (at("component cb=B()", "B"), SemanticCode::WrongTemplate),
        (at("F()(1)", "F"), SemanticCode::WrongTemplate),
        (at("component main=F()", "F"), SemanticCode::WrongTemplate),
    ];
    let mut expected = Vec::new();
    for (start, code) in calls {
        expected.push((code, Severity::Error, 0, start, start + 1));
    }
    expected.sort_by_key(|item| item.3);
    assert_eq!(diagnostic_fingerprint(&result), expected);
}

#[test]
fn duplicate_names_across_include_and_damaged_neighbor_do_not_choose_winner() {
    let root = "include \"lib.circom\"; function Bad( { return 0; } function F(){return 1;} function Use(){return F();}";
    let library = "function F(){return 2;}";
    let result = lower(&[("root.circom", root), ("lib.circom", library)], Version::new(2, 2, 3));
    assert!(!result.syntax_diagnostics.is_empty());
    let root_name = root.find("function F").unwrap() + "function ".len();
    let library_name = library.find("function F").unwrap() + "function ".len();
    assert_eq!(
        diagnostic_fingerprint(&result),
        vec![
            (SemanticCode::DuplicateFunction, Severity::Error, 0, root_name, root_name + 1),
            (SemanticCode::DuplicateFunction, Severity::Error, 1, library_name, library_name + 1),
        ]
    );
    assert!(result.hir.functions().iter().any(|item| item.name == "Use"));
    assert!(result
        .hir
        .expressions()
        .iter()
        .any(|item| matches!(item.call_target(), Some(CallTarget::Ambiguous { .. }))));
}

#[test]
fn shadowing_and_parameter_collision_warn_only_on_actual_collisions() {
    let source = "function F(x,x){var y=1; {var y=2;} return x+y;}";
    let result = lower(&[("shadow.circom", source)], Version::new(2, 2, 3));
    let parameter = source.find("x,x").unwrap() + 2;
    let shadow = source.find("var y=2").unwrap() + 4;
    assert_eq!(
        diagnostic_fingerprint(&result),
        vec![
            (SemanticCode::ParameterCollision, Severity::Warning, 0, parameter, parameter + 1),
            (SemanticCode::Shadowing, Severity::Warning, 0, shadow, shadow + 1),
        ]
    );
    let near = lower(
        &[("near.circom", "function F(x){var y=1; {var z=2;} return x+y;}")],
        Version::new(2, 2, 3),
    );
    assert!(near.diagnostics.is_empty(), "{:?}", near.diagnostics);

    let parameter_shadow = "function F(x){if(1){var x=2;} return x;}";
    let result = lower(&[("parameter_shadow.circom", parameter_shadow)], Version::new(2, 2, 3));
    let start = parameter_shadow.find("var x").unwrap() + 4;
    assert_eq!(
        diagnostic_fingerprint(&result),
        vec![(SemanticCode::Shadowing, Severity::Warning, 0, start, start + 1),]
    );

    let body_shadow = "function F(x){var x=2; return x;}";
    let result = lower(&[("body_shadow.circom", body_shadow)], Version::new(2, 2, 3));
    let start = body_shadow.find("var x").unwrap() + 4;
    assert_eq!(
        diagnostic_fingerprint(&result),
        vec![(SemanticCode::Shadowing, Severity::Warning, 0, start, start + 1),]
    );
}

#[test]
fn malformed_function_construct_is_opaque_without_erasing_neighbor() {
    let source = "function F(){signal s; return 1;} function Good(){return 2;}";
    let result = lower(&[("library.circom", source)], Version::new(2, 2, 3));
    let start = source.find("signal s").unwrap();
    assert_eq!(
        diagnostic_fingerprint(&result),
        vec![(
            SemanticCode::ForbiddenDeclaration,
            Severity::Error,
            0,
            start,
            start + "signal s".len()
        ),]
    );
    assert!(effect_for_function(&result, "F")
        .iter()
        .any(|effect| matches!(effect, Effect::Opaque { .. })));
    assert!(effect_for_function(&result, "Good")
        .iter()
        .any(|effect| matches!(effect, Effect::Return { .. })));
}

#[test]
fn unresolved_anonymous_target_does_not_cascade_input_errors() {
    let source = "template T(){signal output out; out <== Missing()(unknown <== 1);}";
    let result = lower(&[("anon_missing.circom", source)], Version::new(2, 2, 3));
    let start = source.find("Missing").unwrap();
    assert_eq!(
        diagnostic_fingerprint(&result),
        vec![(SemanticCode::MissingCall, Severity::Error, 0, start, start + "Missing".len()),]
    );
    let anonymous = result
        .hir
        .expressions()
        .iter()
        .find(|item| matches!(item.kind, ExprKind::AnonymousComponent { .. }))
        .unwrap();
    assert_eq!(anonymous.knownness, Knownness::Opaque);
}

#[test]
fn anonymous_inputs_reject_duplicate_and_missing_ports() {
    let duplicate = "template Child(){signal input in;} template T(){signal output out; out <== Child()(in <== 1, in <== 2);}";
    let result = lower(&[("duplicate_input.circom", duplicate)], Version::new(2, 2, 3));
    let second = duplicate.rfind("in <== 2").unwrap();
    assert_eq!(
        diagnostic_fingerprint(&result),
        vec![(SemanticCode::AnonymousInput, Severity::Error, 0, second, second + "in <== 2".len()),]
    );
    let missing = "template Child(){signal input a; signal input b;} template T(){signal output out; out <== Child()(a <== 1);}";
    let result = lower(&[("missing_input.circom", missing)], Version::new(2, 2, 3));
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].code, SemanticCode::AnonymousInput);
    assert_eq!(result.diagnostics[0].severity, Severity::Error);
    assert!(result.diagnostics[0].message.contains("every input"));
}

#[test]
fn wrong_arity_and_witness_template_argument_are_opaque() {
    let source = "function F(x){return x;} function G(){return F();} template Child(n){} template T(){signal input x; component c=Child(x);}";
    let result = lower(&[("calls.circom", source)], Version::new(2, 2, 3));
    assert_eq!(
        result.diagnostics.iter().filter(|item| item.code == SemanticCode::WrongArity).count(),
        1
    );
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|item| item.code == SemanticCode::NonComputableExpression)
            .count(),
        1
    );
    assert!(result
        .hir
        .expressions()
        .iter()
        .any(|item| matches!(item.call_target(), Some(CallTarget::Opaque { .. }))));
    assert!(result
        .hir
        .components()
        .iter()
        .any(|item| matches!(item.target, Some(CallTarget::Opaque { .. }))));
    let valid = lower(
        &[("valid.circom", "template Child(n){} template T(){component c=Child(2);}")],
        Version::new(2, 2, 3),
    );
    assert!(valid.diagnostics.is_empty(), "{:?}", valid.diagnostics);
}

#[test]
fn branch_knownness_joins_witness_and_constant_arms() {
    let source = "template T(){signal input x; var n=1; if (x) {n=x;} else {n=2;} signal a[n];}";
    let result = lower(&[("branch.circom", source)], Version::new(2, 2, 3));
    assert!(result
        .diagnostics
        .iter()
        .any(|item| item.code == SemanticCode::NonConstantArrayLength));
    let n = result.hir.symbols().iter().find(|item| item.name == "n").unwrap();
    assert_eq!(n.knownness, Knownness::WitnessDependent);
}

#[test]
fn array_rank_is_checked_before_field_resolution() {
    let source = "template Child(){signal input in;} template T(){component c[2]; c=Child(); signal x; x[0] <== 1; c.in <== 1;}";
    let result = lower(&[("rank.circom", source)], Version::new(2, 2, 3));
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|item| item.code == SemanticCode::InvalidArrayAccess)
            .count(),
        2
    );
    assert!(result.hir.expressions().iter().all(|item| {
        !matches!(&item.kind, ExprKind::Access(path) if path.steps.iter().any(|step| matches!(step, AccessStep::Port { .. })))
    }));
}

#[test]
fn forward_nested_bus_field_resolves_without_expanding_arrays() {
    let source = "template Early(){Outer b; signal output out; out <== b.nested.leaf;} bus Outer(){Inner nested;} bus Inner(){signal leaf;}";
    let result = lower(&[("forward_bus.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(result.hir.expressions().iter().any(|item| matches!(&item.kind, ExprKind::Access(path) if path.steps.iter().filter(|step| matches!(step, AccessStep::Port { .. })).count() == 2)));
}

#[test]
fn arena_ids_are_bound_to_their_own_project() {
    let first = lower(&[("one.circom", "function F(){return 1;}")], Version::new(2, 2, 3));
    let second = lower(&[("two.circom", "function G(){return 2;}")], Version::new(2, 2, 3));
    let first_id = first.hir.functions()[0].id;
    assert_eq!(first.hir.function(first_id).unwrap().name, "F");
    assert!(second.hir.function(first_id).is_none());
}

#[test]
fn missing_root_file_has_path_scoped_incomplete_coverage() {
    let missing = std::env::temp_dir()
        .join(format!("circomspect-hir-missing-root-{}.circom", std::process::id()));
    let loaded = load_sources(
        std::slice::from_ref(&missing),
        &[],
        VersionPolicy::new(Version::new(2, 2, 3)),
    );
    let result = lower_project(&loaded);
    assert!(result.hir.functions().is_empty());
    assert_eq!(result.syntax_diagnostics.len(), 1);
    assert_eq!(result.incomplete.len(), 1);
    assert_eq!(result.incomplete[0].location, IncompleteLocation::Path(missing));
    assert_eq!(result.incomplete[0].reason, IncompleteReason::Include);
}
