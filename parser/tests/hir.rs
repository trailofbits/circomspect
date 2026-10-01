use circomspect_parser::hir::{
    lift_project, AccessStep, BusTarget, CallTarget, ControlGuard, DefinitionRef, Effect, ExprKind,
    IncompleteLocation, IncompleteReason, Knownness, PortSchema, SemanticCode, Severity,
    ValueEvidence,
};
use circomspect_parser::new_frontend::{AssignmentOperator, load_sources, Version, VersionPolicy};
use proptest::prelude::*;
use std::fs;
use std::path::PathBuf;

fn lift(sources: &[(&str, &str)], version: Version) -> circomspect_parser::hir::LiftedProject {
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
    lift_project(&project)
}

fn effect_for<'a>(result: &'a circomspect_parser::hir::LiftedProject, name: &str) -> &'a [Effect] {
    let definition = result.hir.templates().iter().find(|item| item.name == name).unwrap();
    &result.hir.block(definition.body).unwrap().effects
}

fn max_port_steps(result: &circomspect_parser::hir::LiftedProject) -> usize {
    result
        .hir
        .expressions()
        .iter()
        .filter_map(|expression| match &expression.kind {
            ExprKind::Access(path) => Some(
                path.steps.iter().filter(|step| matches!(step, AccessStep::Port { .. })).count(),
            ),
            _ => None,
        })
        .max()
        .unwrap_or(0)
}

fn has_tag_access(result: &circomspect_parser::hir::LiftedProject) -> bool {
    result.hir.expressions().iter().any(|expression| match &expression.kind {
        ExprKind::Access(path) => {
            path.steps.iter().any(|step| matches!(step, AccessStep::Tag { .. }))
        }
        _ => false,
    })
}

#[test]
fn missing_call_initializer_keeps_a_typed_targeted_effect() {
    let result =
        lift(&[("case.circom", "function F(){var t=Missing();return 7;}")], Version::new(2, 2, 3));
    let Some(DefinitionRef::Function(id)) = result.hir.definition("F") else {
        panic!("function F must be present")
    };
    let effects = &result.hir.block(result.hir.function(id).unwrap().body).unwrap().effects;
    assert!(effects.iter().any(|effect| {
        let Effect::OpaqueAssignment { target, value, operator, reason, .. } = effect else {
            return false;
        };
        *operator == AssignmentOperator::Assign
            && *reason == IncompleteReason::UnknownType
            && result.hir.symbol(target.root).is_some_and(|symbol| symbol.name == "t")
            && result.hir.expression(*value).is_some()
    }));
}

#[test]
fn whole_project_resolution_keeps_independent_definitions() {
    let result = lift(
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
    let result = lift(
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
    let source = concat!(
        "template Use() { component c = Later(); signal output out; ",
        "out <== c.visible; out <== c.hidden; } ",
        "template Later() { signal output visible; signal hidden; }"
    );
    let result = lift(&[("main.circom", source)], Version::new(2, 2, 3));
    assert!(max_port_steps(&result) > 0);
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
    let result = lift(
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
    result: &'a circomspect_parser::hir::LiftedProject,
    name: &str,
) -> &'a [Effect] {
    let definition = result.hir.functions().iter().find(|item| item.name == name).unwrap();
    &result.hir.block(definition.body).unwrap().effects
}

#[test]
fn named_anonymous_inputs_keep_checked_destination_and_operator() {
    let source = concat!(
        "template Child() { signal input in; signal output out; out <== in; } ",
        "template Use() { signal output out; out <== Child()(in <== 1); }"
    );
    let result = lift(&[("anonymous.circom", source)], Version::new(2, 2, 3));
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
    let source = concat!(
        "template Child() { signal input in; } template Use() { signal output out; ",
        "out <== Child()(nope <== 1); out <== Child()(in <-- 1); }"
    );
    let result = lift(&[("anonymous.circom", source)], Version::new(2, 2, 3));
    assert_eq!(
        result.diagnostics.iter().filter(|item| item.code == SemanticCode::AnonymousInput).count(),
        2
    );
    assert!(result.incomplete.len() >= 2);
}

#[test]
fn declaration_initializers_keep_witness_and_constraint_effects_distinct() {
    let result = lift(
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
    let result = lift(&[("knownness.circom", source)], Version::new(2, 2, 3));
    let diagnostic = result
        .diagnostics
        .iter()
        .find(|item| item.code == SemanticCode::NonConstantArrayLength)
        .unwrap();
    assert_eq!(diagnostic.severity, Severity::Error);
    assert_eq!(&source[diagnostic.span.start()..diagnostic.span.end()], "n");
    assert!(result.incomplete.iter().any(|item| item.reason == IncompleteReason::NonCompileTime));

    let valid = lift(
        &[("constant.circom", "template T() { var n = 2; signal a[n]; }")],
        Version::new(2, 2, 3),
    );
    assert!(valid.diagnostics.is_empty(), "{:?}", valid.diagnostics);
}

#[test]
fn bus_inline_array_version_check_resolves_through_include() {
    let root = "include \"bus.circom\"; template T() { B b; var a = [b]; }";
    let sources = &[("root.circom", root), ("bus.circom", "bus B() { signal x; }")];
    let old = lift(sources, Version::new(2, 2, 2));
    let version_errors: Vec<_> =
        old.diagnostics.iter().filter(|item| item.code == SemanticCode::FeatureVersion).collect();
    assert_eq!(version_errors.len(), 1, "{:?}", old.diagnostics);
    assert_eq!(version_errors[0].severity, Severity::Error);
    assert_eq!(&root[version_errors[0].span.start()..version_errors[0].span.end()], "[b]");
    let current = lift(sources, Version::new(2, 2, 3));
    assert_eq!(current.diagnostics.len(), 1);
    assert_eq!(current.diagnostics[0].code, SemanticCode::WrongBusAssignment);

    let ordinary = lift(&[("plain.circom", "template T(){var a = [1,2];}")], Version::new(2, 2, 2));
    assert_eq!(ordinary.diagnostics.len(), 1);
    assert_eq!(ordinary.diagnostics[0].code, SemanticCode::WrongAssignmentRank);
}

#[test]
fn local_bus_and_anonymous_array_version_boundaries_are_distinct() {
    let local = "bus B(){signal x;} template T(){B b; var a=[b];}";
    let old = lift(&[("local.circom", local)], Version::new(2, 2, 2));
    assert_eq!(old.diagnostics.len(), 2);
    let version =
        old.diagnostics.iter().find(|item| item.code == SemanticCode::FeatureVersion).unwrap();
    assert_eq!(&local[version.span.start()..version.span.end()], "[b]");
    let current = lift(&[("local.circom", local)], Version::new(2, 2, 3));
    assert_eq!(current.diagnostics.len(), 1);
    assert_eq!(current.diagnostics[0].code, SemanticCode::WrongBusAssignment);

    let anonymous = "template Child(){signal input in;} template T(){var a=[Child()(1)];}";
    let old = lift(&[("anonymous_array.circom", anonymous)], Version::new(2, 2, 2));
    assert!(old.syntax_diagnostics.iter().any(|item| {
        item.kind == circomspect_parser::new_frontend::DiagnosticKind::FeatureVersion
            && item
                .span()
                .is_some_and(|span| &anonymous[span.start()..span.end()] == "[Child()(1)]")
    }));
    let current = lift(&[("anonymous_array.circom", anonymous)], Version::new(2, 2, 3));
    assert!(!current.syntax_diagnostics.iter().any(|item| {
        item.kind == circomspect_parser::new_frontend::DiagnosticKind::FeatureVersion
    }));
}

#[test]
fn unresolved_inline_array_element_type_is_incomplete() {
    let source = "template T(v){var a=[v];}";
    let result = lift(&[("unknown_array.circom", source)], Version::new(2, 2, 2));
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(result.incomplete.iter().any(|item| {
        item.reason == IncompleteReason::UnknownType
            && item.span().is_some_and(|span| &source[span.start()..span.end()] == "[v]")
    }));
}

#[test]
fn bus_type_errors_distinguish_missing_and_wrong_kind() {
    let source = "function F() { return 1; } template T() { F a; Missing b; }";
    let result = lift(&[("bus.circom", source)], Version::new(2, 2, 3));
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
    let source = concat!(
        "template Child(){signal input in; signal output out;} ",
        "template Use(){signal input x; component c = Child(); c.in <== x; c.out <== x;}"
    );
    let result = lift(&[("ports.circom", source)], Version::new(2, 2, 3));
    let effects = effect_for(&result, "Use");
    assert!(effects.iter().any(|effect| {
        match effect {
            Effect::ConstraintAssignment { target, .. } => {
                matches!(target.steps.last(), Some(AccessStep::Port { .. }))
            }
            _ => false,
        }
    }));
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
    let result = lift(&[("tags.circom", source)], Version::new(2, 2, 3));
    let signal = result.hir.symbols().iter().find(|item| item.name == "s").unwrap();
    assert_eq!(signal.knownness, Knownness::WitnessDependent);
    assert!(has_tag_access(&result));
    assert!(result
        .diagnostics
        .iter()
        .any(|item| item.code == SemanticCode::NonConstantArrayLength));
}

#[test]
fn tuple_component_initializers_bind_each_template_call() {
    let source = "template A() {} template B() {} template T() { component (a,b) = (A(),B()); }";
    let result = lift(&[("tuple.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert_eq!(result.hir.components().len(), 2);
    assert!(result
        .hir
        .components()
        .iter()
        .all(|component| matches!(component.target, Some(CallTarget::Template(_)))));
    let invalid = lift(
        &[(
            "bad.circom",
            "template A() {} template B() {} template T() { component (a,b) = (A(),B(),A()); }",
        )],
        Version::new(2, 2, 3),
    );
    assert!(invalid.diagnostics.iter().any(|item| item.code == SemanticCode::InvalidAssignment));
}

fn diagnostic_fingerprint(
    result: &circomspect_parser::hir::LiftedProject,
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
    let source = concat!(
        "function F(){return MissingA();} template T(){component c=MissingT(); ",
        "signal output out; out <== MissingB(MissingC()); ",
        "out <== MissingAnon()(1);} component main=MissingMain();"
    );
    let result = lift(&[("missing.circom", source)], Version::new(2, 2, 3));
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
    assert!(matches!(result.hir.mains()[0].target, CallTarget::Missing { .. }));
}

#[test]
fn wrong_kind_targets_have_exact_directional_codes_and_spans() {
    let source = concat!(
        "function F(){return 1;} template T(){} bus B(){signal x;} ",
        "function Use(){return T()+B();} template Main(){F a; T b; ",
        "component cf=F(); component cb=B(); signal output out; ",
        "out <== F()(1);} component main=F();"
    );
    let result = lift(&[("wrong.circom", source)], Version::new(2, 2, 3));
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
    let root = concat!(
        "include \"lib.circom\"; function Bad( { return 0; } ",
        "function F(){return 1;} function Use(){return F();}"
    );
    let library = "function F(){return 2;}";
    let result = lift(&[("root.circom", root), ("lib.circom", library)], Version::new(2, 2, 3));
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
    let result = lift(&[("shadow.circom", source)], Version::new(2, 2, 3));
    let parameter = source.find("x,x").unwrap() + 2;
    let shadow = source.find("var y=2").unwrap() + 4;
    assert_eq!(
        diagnostic_fingerprint(&result),
        vec![
            (SemanticCode::ParameterCollision, Severity::Warning, 0, parameter, parameter + 1),
            (SemanticCode::Shadowing, Severity::Warning, 0, shadow, shadow + 1),
        ]
    );
    let near = lift(
        &[("near.circom", "function F(x){var y=1; {var z=2;} return x+y;}")],
        Version::new(2, 2, 3),
    );
    assert!(near.diagnostics.is_empty(), "{:?}", near.diagnostics);

    let parameter_shadow = "function F(x){if(1){var x=2;} return x;}";
    let result = lift(&[("parameter_shadow.circom", parameter_shadow)], Version::new(2, 2, 3));
    let start = parameter_shadow.find("var x").unwrap() + 4;
    assert_eq!(
        diagnostic_fingerprint(&result),
        vec![(SemanticCode::Shadowing, Severity::Warning, 0, start, start + 1),]
    );

    let body_shadow = "function F(x){var x=2; return x;}";
    let result = lift(&[("body_shadow.circom", body_shadow)], Version::new(2, 2, 3));
    let start = body_shadow.find("var x").unwrap() + 4;
    assert_eq!(
        diagnostic_fingerprint(&result),
        vec![(SemanticCode::Shadowing, Severity::Warning, 0, start, start + 1),]
    );
}

#[test]
fn malformed_function_construct_is_opaque_without_erasing_neighbor() {
    let source = "function F(){signal s; return 1;} function Good(){return 2;}";
    let result = lift(&[("library.circom", source)], Version::new(2, 2, 3));
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
    let result = lift(&[("anon_missing.circom", source)], Version::new(2, 2, 3));
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
    let duplicate = concat!(
        "template Child(){signal input in;} template T(){signal output out; ",
        "out <== Child()(in <== 1, in <== 2);}"
    );
    let result = lift(&[("duplicate_input.circom", duplicate)], Version::new(2, 2, 3));
    let second = duplicate.rfind("in <== 2").unwrap();
    assert_eq!(
        diagnostic_fingerprint(&result),
        vec![(SemanticCode::AnonymousInput, Severity::Error, 0, second, second + "in <== 2".len()),]
    );
    let missing = concat!(
        "template Child(){signal input a; signal input b;} ",
        "template T(){signal output out; out <== Child()(a <== 1);}"
    );
    let result = lift(&[("missing_input.circom", missing)], Version::new(2, 2, 3));
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].code, SemanticCode::AnonymousInput);
    assert_eq!(result.diagnostics[0].severity, Severity::Error);
    assert!(result.diagnostics[0].message.contains("every input"));
}

#[test]
fn wrong_arity_and_witness_template_argument_are_opaque() {
    let source = concat!(
        "function F(x){return x;} function G(){return F();} template Child(n){} ",
        "template T(){signal input x; component c=Child(x);}"
    );
    let result = lift(&[("calls.circom", source)], Version::new(2, 2, 3));
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
    let valid = lift(
        &[("valid.circom", "template Child(n){} template T(){component c=Child(2);}")],
        Version::new(2, 2, 3),
    );
    assert!(valid.diagnostics.is_empty(), "{:?}", valid.diagnostics);
}

#[test]
fn branch_knownness_joins_witness_and_constant_arms() {
    let source = "template T(){signal input x; var n=1; if (x) {n=x;} else {n=2;} signal a[n];}";
    let result = lift(&[("branch.circom", source)], Version::new(2, 2, 3));
    assert!(result
        .diagnostics
        .iter()
        .any(|item| item.code == SemanticCode::NonConstantArrayLength));
    let n = result.hir.symbols().iter().find(|item| item.name == "n").unwrap();
    assert_eq!(n.knownness, Knownness::WitnessDependent);
}

#[test]
fn array_rank_is_checked_before_field_resolution() {
    let source = concat!(
        "template Child(){signal input in;} template T(){component c[2]; c=Child(); ",
        "signal x; x[0] <== 1; c.in <== 1;}"
    );
    let result = lift(&[("rank.circom", source)], Version::new(2, 2, 3));
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|item| item.code == SemanticCode::InvalidArrayAccess)
            .count(),
        2
    );
    assert_eq!(max_port_steps(&result), 0);
}

#[test]
fn component_array_rejects_mixed_template_targets() {
    let source = concat!(
        "template A(){signal output out;} template B(){signal output out;} ",
        "template Check(){component c[2]; c[0]=A(); c[1]=B(); ",
        "signal output y; y <== c[0].out;}"
    );
    let result = lift(&[("mixed.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.iter().any(|item| item.code == SemanticCode::InvalidAssignment));
    assert!(!result.hir.expressions().iter().any(|expression| {
        let ExprKind::Access(path) = &expression.kind else { return false };
        result.hir.symbol(path.root).is_some_and(|symbol| symbol.name == "c")
            && path.component_output
    }));
    assert!(!result
        .hir
        .expressions()
        .iter()
        .any(|expression| { matches!(expression.call_target(), Some(CallTarget::Template(_))) }));
}

#[test]
fn later_mixed_component_target_invalidates_earlier_call_and_port_read() {
    let source = concat!(
        "template A(){signal output out;} template B(){signal output out;} ",
        "template Check(){component c[2]; c[0]=A(); signal x; x <== c[0].out; ",
        "c[1]=B();}"
    );
    let result = lift(&[("late_mixed.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.iter().any(|item| item.code == SemanticCode::InvalidAssignment));
    assert!(!result
        .hir
        .expressions()
        .iter()
        .any(|expression| { matches!(expression.call_target(), Some(CallTarget::Template(_))) }));
    assert!(!result.hir.expressions().iter().any(|expression| {
        let ExprKind::Access(path) = &expression.kind else { return false };
        result.hir.symbol(path.root).is_some_and(|symbol| symbol.name == "c")
    }));
}

#[test]
fn mixed_component_target_preserves_independent_deferred_variable_write() {
    let source = concat!(
        "template A(){} template B(){} ",
        "template Check(n){var t=n;component c[2];c[0]=A();c[1]=B();}"
    );
    let result = lift(&[("mixed_deferred.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.iter().any(|item| item.code == SemanticCode::InvalidAssignment));
    assert!(effect_for(&result, "Check").iter().any(|effect| {
        let Effect::DeferredVariableAssignment { target, .. } = effect else { return false };
        result.hir.symbol(target.root).is_some_and(|symbol| symbol.name == "t")
    }));
}

#[test]
fn component_array_keeps_one_template_with_distinct_parameters() {
    let source = concat!(
        "template Child(n){signal output out; out <== n;} ",
        "template Check(){component c[2]; c[0]=Child(1); c[1]=Child(2); ",
        "signal output y; y <== c[0].out + c[1].out;}"
    );
    let result = lift(&[("same.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert_eq!(
        result
            .hir
            .expressions()
            .iter()
            .filter(|expression| {
                let ExprKind::Access(path) = &expression.kind else { return false };
                result.hir.symbol(path.root).is_some_and(|symbol| symbol.name == "c")
                    && path.component_output
            })
            .count(),
        2
    );
}

#[test]
fn component_branches_reject_different_template_targets() {
    let source = concat!(
        "template A(){signal output out;} template B(){signal output out;} ",
        "template Check(n){component c; if(n){c=A();} else {c=B();} ",
        "signal output y; y <== c.out;}"
    );
    let result = lift(&[("branches.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.iter().any(|item| item.code == SemanticCode::InvalidAssignment));
    assert!(!result.hir.expressions().iter().any(|expression| {
        let ExprKind::Access(path) = &expression.kind else { return false };
        result.hir.symbol(path.root).is_some_and(|symbol| symbol.name == "c")
            && path.component_output
    }));
    assert!(!result
        .hir
        .expressions()
        .iter()
        .any(|expression| { matches!(expression.call_target(), Some(CallTarget::Template(_))) }));
}

#[test]
fn forward_nested_bus_field_resolves_without_expanding_arrays() {
    let source = concat!(
        "template Early(){Outer b; signal output out; out <== b.nested.leaf;} ",
        "bus Outer(){Inner nested;} bus Inner(){signal leaf;}"
    );
    let result = lift(&[("forward_bus.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert_eq!(max_port_steps(&result), 2);
}

#[test]
fn arena_ids_are_bound_to_their_own_project() {
    let first = lift(&[("one.circom", "function F(){return 1;}")], Version::new(2, 2, 3));
    let second = lift(&[("two.circom", "function G(){return 2;}")], Version::new(2, 2, 3));
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
    let result = lift_project(&loaded);
    assert!(result.hir.functions().is_empty());
    assert_eq!(result.syntax_diagnostics.len(), 1);
    assert_eq!(result.incomplete.len(), 1);
    assert_eq!(result.incomplete[0].location, IncompleteLocation::Path(missing));
    assert_eq!(result.incomplete[0].reason, IncompleteReason::Include);
}

#[test]
fn loop_condition_changed_to_witness_is_opaque() {
    let source = concat!(
        "template T(){signal input x; var n=1; while(n<3){n=x; x===x;} ",
        "for(var i=0;i<2;i++){i=x; x===x;}}"
    );
    let result = lift(&[("loop_knownness.circom", source)], Version::new(2, 2, 3));
    let effects = effect_for(&result, "T");
    assert_eq!(
        effects
            .iter()
            .filter(|effect| matches!(effect, Effect::While { .. } | Effect::For { .. }))
            .count(),
        0
    );
    assert_eq!(
        effects
            .iter()
            .filter(|effect| matches!(
                effect,
                Effect::Opaque { reason: IncompleteReason::NonCompileTime, .. }
            ))
            .count(),
        2
    );
}

#[test]
fn forward_port_with_wrong_bus_arity_does_not_resolve_field() {
    let source = concat!(
        "template Early(){Outer b; signal output out; out <== b.nested.leaf;} ",
        "bus Outer(){Inner(1,2) nested;} bus Inner(n){signal leaf;}"
    );
    let result = lift(&[("stale_bus.circom", source)], Version::new(2, 2, 3));
    assert_eq!(
        result.diagnostics.iter().filter(|item| item.code == SemanticCode::WrongArity).count(),
        1
    );
    assert!(max_port_steps(&result) < 2);
    assert!(result.incomplete.iter().any(|item| item.reason == IncompleteReason::UnknownType));
}

#[test]
fn duplicate_local_declaration_is_opaque_and_keeps_first_binding() {
    let source = "function F(){var x=1; var x=2; return x;}";
    let result = lift(&[("duplicate_local.circom", source)], Version::new(2, 2, 3));
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].code, SemanticCode::DuplicateSymbol);
    assert_eq!(&source[result.diagnostics[0].span.start()..result.diagnostics[0].span.end()], "x");
    let effects = effect_for_function(&result, "F");
    assert_eq!(
        effects.iter().filter(|effect| matches!(effect, Effect::Declaration { .. })).count(),
        1
    );
    assert!(effects.iter().any(|effect| {
        matches!(effect, Effect::Opaque {
            reason: IncompleteReason::AmbiguousReference(name), ..
        } if name == "x")
    }));
}

#[test]
fn whole_array_tag_resolves_but_indexed_tag_is_invalid() {
    let source =
        "template T(){signal input {binary} s[2]; var good=s.binary; var bad=s[0].binary;}";
    let result = lift(&[("array_tag.circom", source)], Version::new(2, 2, 3));
    assert_eq!(result.diagnostics.len(), 1, "{:?}", result.diagnostics);
    assert_eq!(result.diagnostics[0].code, SemanticCode::InvalidTagAfterArray);
    assert_eq!(
        &source[result.diagnostics[0].span.start()..result.diagnostics[0].span.end()],
        ".binary"
    );
    assert!(has_tag_access(&result));
}

#[test]
fn duplicate_template_ports_cannot_be_selected_by_access_or_anonymous_input() {
    let source = concat!(
        "template Child(){signal input x; signal input x;} ",
        "template Use(){component c=Child(); c.x <== 1; var a=Child()(x <== 2);}"
    );
    let result = lift(&[("duplicate_ports.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.iter().any(|item| item.code == SemanticCode::DuplicateSymbol));
    assert_eq!(max_port_steps(&result), 0);
    let anonymous = result
        .hir
        .expressions()
        .iter()
        .find(|item| matches!(item.kind, ExprKind::AnonymousComponent { .. }))
        .unwrap();
    let ExprKind::AnonymousComponent { inputs, .. } = &anonymous.kind else { unreachable!() };
    assert!(inputs.iter().all(|input| input.resolved_port().is_none()));
    assert_eq!(anonymous.knownness, Knownness::Opaque);
}

#[test]
fn preindexed_parameter_name_does_not_hide_shadowed_bus_argument() {
    let source = concat!(
        "bus Inner(n){signal leaf;} template Early(){component c=Later(1); ",
        "signal output o; o <== c.b.leaf;} template Later(n){signal input x; ",
        "var n=x; Inner(n) output b;}"
    );
    let result = lift(&[("shadowed_bus.circom", source)], Version::new(2, 2, 3));
    assert!(max_port_steps(&result) < 2);
    assert!(result.incomplete.iter().any(|item| item.reason == IncompleteReason::UnknownType));
}

#[test]
fn locally_proven_bus_argument_recovers_after_conservative_preindex() {
    let source = concat!(
        "bus Inner(n){signal leaf;} template T(){var n=1; Inner(n) output b; ",
        "signal output o; o <== b.leaf;}"
    );
    let result = lift(&[("local_bus_arg.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(max_port_steps(&result) > 0);
}

#[test]
fn unshadowed_parameter_bus_port_resolves_forward() {
    let source = concat!(
        "bus Inner(n){signal leaf;} template Early(){component c=Later(1); ",
        "signal output o; o <== c.b.leaf;} ",
        "template Later(n){Inner(n) output b;}"
    );
    let result = lift(&[("parameter_bus.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert_eq!(max_port_steps(&result), 2);
}

#[test]
fn unresolved_function_call_keeps_inline_array_type_unknown() {
    let source = "template T(){var a=[Unknown()];}";
    let result = lift(&[("unknown_array_call.circom", source)], Version::new(2, 2, 2));
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].code, SemanticCode::MissingCall);
    assert!(result.incomplete.iter().any(|item| {
        item.reason == IncompleteReason::UnknownType
            && matches!(&item.location, IncompleteLocation::Source(span)
                if &source[span.start()..span.end()] == "[Unknown()]")
    }));
    let nested = "template T(){var a=[Unknown()+1];}";
    let nested_result = lift(&[("nested_unknown_array.circom", nested)], Version::new(2, 2, 2));
    assert!(nested_result.incomplete.iter().any(|item| {
        item.reason == IncompleteReason::UnknownType
            && matches!(&item.location, IncompleteLocation::Source(span)
                if &nested[span.start()..span.end()] == "[Unknown()+1]")
    }));
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]
    #[test]
    fn duplicates_remain_ambiguous(indices in proptest::collection::vec(0u8..6, 1..8)) {
        let mut source = String::new();
        let mut counts = [0usize; 6];
        for index in &indices {
            source.push_str(&format!("function F{index}(){{return 1;}} "));
            counts[usize::from(*index)] += 1;
        }
        source.push_str("function Unique(){return 2;}");
        let result = lift(&[("generated.circom", &source)], Version::new(2, 2, 3));
        let duplicate_declarations: usize = counts.iter().filter(|count| **count > 1).sum();
        prop_assert_eq!(result.diagnostics.len(), duplicate_declarations);
        prop_assert!(result.hir.definition("Unique").is_some());
        for (index, count) in counts.iter().enumerate() {
            let name = format!("F{index}");
            prop_assert_eq!(result.hir.definitions_named(&name).len(), *count);
            prop_assert_eq!(result.hir.definition(&name).is_some(), *count == 1);
        }
    }
}

#[test]
fn indexed_writes_and_reads_propagate_witness_knownness() {
    let source = concat!(
        "template T(){signal input i; var a[2]=[1,2]; a[0]=i; a[1]=1; ",
        "signal first[a[0]]; var b[2]=[1,2]; b[i]=3; signal second[b[0]]; ",
        "var c[2]=[1,2]; signal third[c[i]]; var d[2]; d[0]=1; signal fourth[d[1]];}"
    );
    let result = lift(&[("indexed_knownness.circom", source)], Version::new(2, 2, 3));
    assert_eq!(
        result
            .diagnostics
            .iter()
            .filter(|item| item.code == SemanticCode::NonConstantArrayLength)
            .count(),
        3
    );
    assert!(result.incomplete.iter().any(|item| {
        item.reason == IncompleteReason::NonCompileTime
            && matches!(&item.location, IncompleteLocation::Source(span)
                if &source[span.start()..span.end()] == "d[1]")
    }));
}

#[test]
fn parallel_component_and_main_keep_modifier() {
    let source = concat!(
        "template Child(){} template T(){component c=parallel Child();} ",
        "component main=parallel T();"
    );
    let result = lift(&[("parallel.circom", source)], Version::new(2, 2, 3));
    assert!(result.syntax_diagnostics.is_empty(), "{:?}", result.syntax_diagnostics);
    assert!(result
        .hir
        .expressions()
        .iter()
        .any(|item| { matches!(item.kind, ExprKind::Parallel(_)) }));
    assert_eq!(result.hir.mains().len(), 1);
    assert!(result.hir.mains()[0].parallel);
}

#[test]
fn invalid_call_rhs_never_creates_constraint_effect() {
    let source = concat!(
        "template T(){signal output out; out <== Missing(); ",
        "out <== 1; Missing() === 2;}"
    );
    let result = lift(&[("invalid_rhs.circom", source)], Version::new(2, 2, 3));
    assert_eq!(
        result.diagnostics.iter().filter(|item| item.code == SemanticCode::MissingCall).count(),
        2
    );
    let effects = effect_for(&result, "T");
    assert_eq!(
        effects.iter().filter(|item| matches!(item, Effect::ConstraintAssignment { .. })).count(),
        1
    );
    assert_eq!(
        effects.iter().filter(|item| matches!(item, Effect::EqualityConstraint { .. })).count(),
        0
    );
    assert_eq!(effects.iter().filter(|item| matches!(item, Effect::Opaque { .. })).count(), 2);
}

#[test]
fn invalid_nested_index_and_missing_anonymous_input_cannot_certify_constraint() {
    let source = concat!(
        "template Child(){signal input a; signal input b;} ",
        "template T(){signal s[2]; signal output out; ",
        "out <== s[Missing()]; out <== Child()(a <== 1);}"
    );
    let result = lift(&[("invalid_nested.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.iter().any(|item| item.code == SemanticCode::MissingCall));
    assert!(result.diagnostics.iter().any(|item| item.code == SemanticCode::AnonymousInput));
    let effects = effect_for(&result, "T");
    assert_eq!(
        effects.iter().filter(|item| matches!(item, Effect::ConstraintAssignment { .. })).count(),
        0
    );
}

#[test]
fn colliding_bus_tag_and_field_is_not_falsely_resolved_as_tag() {
    let source = "bus B(){signal x;} template T(){B {x} b; var value=b.x;}";
    let result = lift(&[("bus_tag_collision.circom", source)], Version::new(2, 2, 3));
    assert!(result.syntax_diagnostics.is_empty(), "{:?}", result.syntax_diagnostics);
    assert!(result
        .incomplete
        .iter()
        .any(|item| { item.reason == IncompleteReason::AmbiguousReference("x".into()) }));
    assert!(result.hir.expressions().iter().all(|item| {
        !matches!(&item.kind, ExprKind::Access(path)
            if path.steps.iter().any(|step| matches!(step, AccessStep::Tag { .. })))
    }));
}

#[test]
fn invalid_assignment_index_cannot_certify_constraint() {
    let source = "template T(){signal output out[2]; out[Missing()] <== 1;}";
    let result = lift(&[("invalid_lhs_index.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.iter().any(|item| item.code == SemanticCode::MissingCall));
    let effects = effect_for(&result, "T");
    assert!(effects.iter().all(|item| !matches!(item, Effect::ConstraintAssignment { .. })));
}

#[test]
fn external_component_input_tag_has_its_own_diagnostic_code() {
    let source = concat!(
        "template Child(){signal input {binary} x;} ",
        "template T(){component c=Child(); var t=c.x.binary;}"
    );
    let result = lift(&[("external_tag.circom", source)], Version::new(2, 2, 3));
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(result.diagnostics[0].code, SemanticCode::InputTagAccess);
    assert_eq!(result.diagnostics[0].severity, Severity::Error);
    let span = result.diagnostics[0].span;
    assert_eq!(&source[span.start()..span.end()], "binary");
}

#[test]
fn invalid_dimension_makes_local_declaration_and_access_opaque() {
    let source =
        concat!("template T(){signal input x; signal a[x]; signal output o; ", "o<==a[0];}");
    let result = lift(&[("invalid_shape.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.iter().any(|item| {
        item.code == SemanticCode::NonConstantArrayLength
            && &source[item.span.start()..item.span.end()] == "x"
    }));
    let symbol = result.hir.symbols().iter().find(|item| item.name == "a").unwrap();
    assert!(!symbol.shape_checked);
    let effects = effect_for(&result, "T");
    assert!(effects.iter().all(|item| { !matches!(item, Effect::ConstraintAssignment { .. }) }));
}

#[test]
fn invalid_forward_port_dimension_does_not_resolve_checked_access() {
    let source = concat!(
        "bus Inner(){signal leaf;} template Early(){component c=Later(); ",
        "signal output o; o<==c.b[0].leaf;} template Later(){signal input x; ",
        "Inner() output b[x];}"
    );
    let result = lift(&[("forward_shape.circom", source)], Version::new(2, 2, 3));
    assert!(result
        .diagnostics
        .iter()
        .any(|item| { item.code == SemanticCode::NonConstantArrayLength }));
    assert!(max_port_steps(&result) < 2);
    assert!(effect_for(&result, "Early")
        .iter()
        .all(|item| !matches!(item, Effect::ConstraintAssignment { .. })));
}

#[test]
fn external_port_schema_does_not_change_with_definition_order() {
    let later = concat!("template Later(){var n=1; signal output p[n]; ", "Inner(n) output b;}");
    let early = concat!(
        "template Early(){component c=Later(); signal output o; ",
        "o<==c.p[0]; o<==c.b.leaf;}"
    );
    let bus = "bus Inner(n){signal leaf;}";
    let before = format!("{bus} {early} {later}");
    let after = format!("{bus} {later} {early}");
    for source in [&before, &after] {
        let result = lift(&[("order.circom", source)], Version::new(2, 2, 3));
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        assert_eq!(max_port_steps(&result), 0);
        let later = result.hir.templates().iter().find(|item| item.name == "Later").unwrap();
        for port_id in &later.ports {
            let port = result.hir.port(*port_id).unwrap();
            assert!(matches!(port.schema, PortSchema::Opaque(_)));
            let symbol = result.hir.symbol(port.symbol).unwrap();
            assert!(symbol.shape_checked);
        }
        assert!(effect_for(&result, "Early")
            .iter()
            .all(|item| !matches!(item, Effect::ConstraintAssignment { .. })));
    }
}

#[test]
fn anonymous_input_with_invalid_public_shape_remains_opaque() {
    let source = concat!(
        "template Child(){signal input n; signal input x[n];} ",
        "template T(){signal output out; out<==Child()(n<==2,x<==3);}"
    );
    let result = lift(&[("anonymous_shape.circom", source)], Version::new(2, 2, 3));
    assert!(result
        .diagnostics
        .iter()
        .any(|item| { item.code == SemanticCode::NonConstantArrayLength }));
    let anonymous = result
        .hir
        .expressions()
        .iter()
        .find(|item| matches!(item.kind, ExprKind::AnonymousComponent { .. }))
        .unwrap();
    let ExprKind::AnonymousComponent { inputs, .. } = &anonymous.kind else { unreachable!() };
    assert!(inputs.iter().any(|input| input.resolved_port().is_none()));
    assert_eq!(anonymous.knownness, Knownness::Opaque);
    assert!(effect_for(&result, "T")
        .iter()
        .all(|item| !matches!(item, Effect::ConstraintAssignment { .. })));
}

#[test]
fn incompatible_assignments_do_not_generate_constraints() {
    let cases = [
        ("bus B(){signal x;} template T(){B b; b<==1;}", "b<==1", SemanticCode::WrongBusAssignment),
        (
            "bus B(){signal x;} template T(){B b; signal output out; out<==b;}",
            "out<==b",
            SemanticCode::WrongBusAssignment,
        ),
        (
            "bus B(){signal x;} bus C(){signal x;} template T(){B b; C c; b<==c;}",
            "b<==c",
            SemanticCode::WrongBusAssignment,
        ),
        (
            "bus B(){signal x;} bus C(){signal x;} template T(){B b[2]; C c; b<==c;}",
            "b<==c",
            SemanticCode::WrongAssignmentRank,
        ),
        (
            "template T(){signal a[2]; signal output out; out<==a;}",
            "out<==a",
            SemanticCode::WrongAssignmentRank,
        ),
    ];
    for (source, assignment, code) in cases {
        let result = lift(&[("mismatch.circom", source)], Version::new(2, 2, 3));
        assert_eq!(result.diagnostics.len(), 1, "{:?}", result.diagnostics);
        let diagnostic = &result.diagnostics[0];
        assert_eq!(diagnostic.code, code);
        assert_eq!(diagnostic.severity, Severity::Error);
        assert_eq!(&source[diagnostic.span.start()..diagnostic.span.end()], assignment);
        assert!(effect_for(&result, "T")
            .iter()
            .all(|item| !matches!(item, Effect::ConstraintAssignment { .. })));
    }
}

#[test]
fn matching_bus_and_array_shapes_keep_checked_assignments() {
    let source = concat!(
        "bus B(){signal x;} template T(){B input source; B output target; ",
        "signal input a[2]; signal output b[2]; target<==source; b<==a;}"
    );
    let result = lift(&[("matching.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert_eq!(
        effect_for(&result, "T")
            .iter()
            .filter(|item| matches!(item, Effect::ConstraintAssignment { .. }))
            .count(),
        2
    );
}

#[test]
fn incompatible_anonymous_input_is_not_checked() {
    let source = concat!(
        "bus B(){signal x;} template Child(){B input b; signal output out; out<==b.x;} ",
        "template T(){var a=Child()(b<==1);}"
    );
    let result = lift(&[("anonymous_type.circom", source)], Version::new(2, 2, 3));
    let start = source.find("b<==1").unwrap();
    assert_eq!(
        diagnostic_fingerprint(&result),
        vec![(SemanticCode::WrongBusAssignment, Severity::Error, 0, start, start + 5)]
    );
    let anonymous = result
        .hir
        .expressions()
        .iter()
        .find(|item| matches!(item.kind, ExprKind::AnonymousComponent { .. }))
        .unwrap();
    let ExprKind::AnonymousComponent { inputs, .. } = &anonymous.kind else { unreachable!() };
    assert_eq!(anonymous.knownness, Knownness::Opaque);
    assert_eq!(inputs.len(), 1);
    assert!(inputs[0].resolved_port().is_none());
}

#[test]
fn incompatible_bus_arithmetic_and_equality_cannot_certify_constraints() {
    let cases = [
        "bus B(){signal x;} template T(){B b; b===1;}",
        "bus B(){signal x;} bus C(){signal x;} template T(){B b; C c; b===c;}",
        "bus B(){signal x;} template T(){B b; signal output out; out<==b+1;}",
        "bus B(){signal x;} template T(){B b; signal output out; out<==-b;}",
        "bus B(){signal x;} template T(){B b; signal output out; out<==b?1:2;}",
    ];
    for source in cases {
        let result = lift(&[("arithmetic.circom", source)], Version::new(2, 2, 3));
        assert!(effect_for(&result, "T").iter().all(|item| {
            !matches!(item, Effect::EqualityConstraint { .. } | Effect::ConstraintAssignment { .. })
        }));
    }
}

#[test]
fn matching_bus_equality_remains_a_checked_constraint() {
    let source = "bus B(){signal x;} template T(){B a; B b; a===b;}";
    let result = lift(&[("bus_equality.circom", source)], Version::new(2, 2, 3));
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert!(effect_for(&result, "T")
        .iter()
        .any(|item| matches!(item, Effect::EqualityConstraint { .. })));
}

#[test]
fn bus_and_array_indices_cannot_certify_accesses() {
    let invalid = [
        (
            "bus B(){signal x;} template T(){signal a[2]; B b; a[b]<==1;}",
            "b",
            SemanticCode::InvalidArrayIndexBus,
        ),
        (
            "template T(){signal a[2]; signal i[2]; a[i]<==1;}",
            "i",
            SemanticCode::InvalidArrayIndexDimension,
        ),
    ];
    for (source, index, code) in invalid {
        let result = lift(&[("index.circom", source)], Version::new(2, 2, 3));
        assert!(effect_for(&result, "T")
            .iter()
            .all(|item| !matches!(item, Effect::ConstraintAssignment { .. })));
        assert_eq!(result.diagnostics.len(), 1, "{:?}", result.diagnostics);
        let diagnostic = &result.diagnostics[0];
        assert_eq!(diagnostic.code, code);
        assert_eq!(diagnostic.severity, Severity::Error);
        assert_eq!(&source[diagnostic.span.start()..diagnostic.span.end()], index);
    }
    let valid = "template T(){signal a[2]; signal input i; var j=0; a[i]<==1; a[j]<==2;}";
    let result = lift(&[("valid_index.circom", valid)], Version::new(2, 2, 3));
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert_eq!(
        effect_for(&result, "T")
            .iter()
            .filter(|item| matches!(item, Effect::ConstraintAssignment { .. }))
            .count(),
        2
    );
}

#[test]
fn variable_assignments_require_compatible_shapes() {
    let invalid = [
        ("bus B(){signal x;} template T(){B b; var v=b;}", SemanticCode::WrongBusAssignment),
        ("template T(){var a[2]; a=1;}", SemanticCode::WrongAssignmentRank),
    ];
    for (source, code) in invalid {
        let result = lift(&[("variable_shape.circom", source)], Version::new(2, 2, 3));
        assert_eq!(result.diagnostics.len(), 1, "{:?}", result.diagnostics);
        assert_eq!(result.diagnostics[0].code, code);
        assert!(effect_for(&result, "T")
            .iter()
            .all(|item| !matches!(item, Effect::VariableAssignment { .. })));
    }
    let valid = "template T(){var n=1; var a[2]=[1,2]; n=3; a=[4,5];}";
    let result = lift(&[("valid_variable.circom", valid)], Version::new(2, 2, 3));
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    assert_eq!(
        effect_for(&result, "T")
            .iter()
            .filter(|item| matches!(item, Effect::VariableAssignment { .. }))
            .count(),
        4
    );
}

#[test]
fn array_condition_is_opaque_but_scalar_condition_is_checked() {
    let invalid = "function F(){if([1,2]){return 1;} return 0;}";
    let result = lift(&[("array_condition.circom", invalid)], Version::new(2, 2, 3));
    assert!(effect_for_function(&result, "F")
        .iter()
        .all(|item| !matches!(item, Effect::If { .. })));
    let valid = "function F(){if(1){return 1;} return 0;}";
    let result = lift(&[("scalar_condition.circom", valid)], Version::new(2, 2, 3));
    assert!(effect_for_function(&result, "F").iter().any(|item| matches!(item, Effect::If { .. })));
}

#[test]
fn parameter_dependent_branches_keep_their_blocks() {
    let source = concat!(
        "template T(n){signal output o;if(n){o<==1;}else{o<==2;}} ",
        "function F(n){var x=0;if(n<2){x=1;}else{x=2;}return x;}"
    );
    let result = lift(&[("deferred_if.circom", source)], Version::new(2, 2, 3));
    for effects in [effect_for(&result, "T"), effect_for_function(&result, "F")] {
        let Some(Effect::If { condition, then_block, else_block: Some(else_block), guard, .. }) =
            effects.iter().find(|effect| matches!(effect, Effect::If { .. }))
        else {
            panic!("parameter branch was discarded: {effects:?}");
        };
        assert_eq!(*guard, ControlGuard::DeferredScalar);
        assert!(!result.hir.block(*then_block).unwrap().effects.is_empty());
        assert!(!result.hir.block(*else_block).unwrap().effects.is_empty());
        assert!(!matches!(result.hir.expression(*condition).unwrap().kind, ExprKind::Opaque(_)));
    }
}

#[test]
fn resolved_function_guard_defers_shape_only_for_compile_time_arguments() {
    let source = concat!(
        "function Id(x){return x;}",
        "template Good(n){signal output o;if(Id(n)){o<==1;}else{o<==2;}}",
        "template Bad(){signal input x;signal output o;if(Id(x)){o<==1;}}"
    );
    let result = lift(&[("call_guard.circom", source)], Version::new(2, 2, 3));
    assert!(effect_for(&result, "Good")
        .iter()
        .any(|effect| matches!(effect, Effect::If { guard: ControlGuard::DeferredScalar, .. })));
    assert!(effect_for(&result, "Bad").iter().all(|effect| !matches!(effect, Effect::If { .. })));
}

#[test]
fn invalid_parameter_shape_does_not_become_control() {
    let invalid = "function F(n){if(n+[1,2]){return 1;}return 0;}";
    let result = lift(&[("invalid_guard.circom", invalid)], Version::new(2, 2, 3));
    assert!(effect_for_function(&result, "F")
        .iter()
        .all(|effect| !matches!(effect, Effect::If { .. })));
}

#[test]
fn parameter_dependent_loops_keep_their_control_edges() {
    let source = "function F(n){var x=0;while(n){x++;}for(var i=0;i<n;i++){x++;}return x;}";
    let result = lift(&[("deferred_loops.circom", source)], Version::new(2, 2, 3));
    let effects = effect_for_function(&result, "F");
    assert!(effects
        .iter()
        .any(|effect| matches!(effect, Effect::While { guard: ControlGuard::DeferredScalar, .. })));
    assert!(effects
        .iter()
        .any(|effect| matches!(effect, Effect::For { guard: ControlGuard::DeferredScalar, .. })));
}

#[test]
fn witness_control_preserves_only_constraint_free_branches() {
    let source = concat!(
        "template T(){signal input x;signal output y;var v=0;",
        "if(x){v=1;}else{v=2;}if(x){y<==1;}}"
    );
    let result = lift(&[("witness_if.circom", source)], Version::new(2, 2, 3));
    let effects = effect_for(&result, "T");
    assert!(effects
        .iter()
        .any(|effect| matches!(effect, Effect::If { guard: ControlGuard::WitnessOnly, .. })));
    assert!(effects.iter().any(|effect| matches!(
        effect,
        Effect::Opaque { reason: IncompleteReason::NonCompileTime, .. }
    )));
}

#[test]
fn witness_control_rejects_anonymous_component_hidden_in_assignment() {
    let source = concat!(
        "template Child(){signal input in;signal output out;out<==in;}",
        "template Parent(){signal input gate;signal output out;",
        "if(gate){out <-- Child()(in <== 1);}}"
    );
    let result = lift(&[("anonymous_guard.circom", source)], Version::new(2, 2, 3));
    let effects = effect_for(&result, "Parent");
    assert!(effects.iter().all(|effect| !matches!(effect, Effect::If { .. })));
    assert!(effects.iter().any(|effect| matches!(
        effect,
        Effect::Opaque { reason: IncompleteReason::NonCompileTime, .. }
    )));
}

#[test]
fn witness_guard_with_unproved_parameter_shape_stays_opaque() {
    let source = "template T(n){signal input x;var v=0;if(n+x){v=1;}else{v=2;}}";
    let result = lift(&[("deferred_witness_guard.circom", source)], Version::new(2, 2, 3));
    let effects = effect_for(&result, "T");
    assert!(effects.iter().all(|effect| !matches!(effect, Effect::If { .. })));
    assert!(effects.iter().any(|effect| matches!(
        effect,
        Effect::Opaque { reason: IncompleteReason::UnknownType, .. }
    )));
}

#[test]
fn unresolved_function_result_keeps_assignment_target_and_call() {
    let source = "function F(a){return a;} template T(){signal input x;signal output y;y<==F(x);}";
    let result = lift(&[("opaque_call.circom", source)], Version::new(2, 2, 3));
    let effects = effect_for(&result, "T");
    let Some(Effect::OpaqueAssignment { target, value, operator, reason, .. }) = effects.last()
    else {
        panic!("expected target-aware opaque assignment")
    };
    assert_eq!(result.hir.symbol(target.root).unwrap().name, "y");
    assert_eq!(*operator, AssignmentOperator::Constraint);
    assert_eq!(*reason, IncompleteReason::UnknownType);
    let Some(expression) = result.hir.expression(*value) else { panic!("call expression") };
    assert!(matches!(expression.kind, ExprKind::Call { .. }));
}

#[test]
fn parameter_shaped_variable_write_keeps_deferred_guard() {
    let source = "function F(n){var x=n;if(x){return 1;}return 0;}";
    let result = lift(&[("deferred_var.circom", source)], Version::new(2, 2, 3));
    let effects = effect_for_function(&result, "F");
    let Some(Effect::DeferredVariableAssignment { target, value, .. }) =
        effects.iter().find(|effect| matches!(effect, Effect::DeferredVariableAssignment { .. }))
    else {
        panic!("parameter-shaped write must remain targeted")
    };
    assert_eq!(result.hir.symbol(target.root).unwrap().name, "x");
    assert!(matches!(result.hir.expression(*value).unwrap().kind, ExprKind::Access(_)));
    assert_eq!(result.hir.symbol(target.root).unwrap().value_evidence, ValueEvidence::Deferred);
    assert!(effects
        .iter()
        .any(|effect| matches!(effect, Effect::If { guard: ControlGuard::DeferredScalar, .. })));
}

#[test]
fn later_scalar_overwrite_does_not_erase_deferred_variable_evidence() {
    let source = "function F(n){var x=n;x=0;if(x){return 1;}return 0;}";
    let result = lift(&[("deferred_overwrite.circom", source)], Version::new(2, 2, 3));
    let effects = effect_for_function(&result, "F");
    assert!(effects
        .iter()
        .any(|effect| matches!(effect, Effect::If { guard: ControlGuard::DeferredScalar, .. })));
    let x = result.hir.symbols().iter().find(|symbol| symbol.name == "x").unwrap();
    assert_eq!(x.value_evidence, ValueEvidence::Deferred);
}

#[test]
fn deferred_shape_propagates_through_copy_arithmetic_and_select() {
    for assigned in ["x", "x+1", "1 ? x : 2"] {
        let source =
            format!("function F(n){{var x=n;var y={assigned};if(y){{return 1;}}return 0;}}");
        let result = lift(&[("deferred_transitive.circom", &source)], Version::new(2, 2, 3));
        let effects = effect_for_function(&result, "F");
        assert!(
            effects.iter().any(|effect| matches!(
                effect,
                Effect::DeferredVariableAssignment { target, .. }
                    if result.hir.symbol(target.root).unwrap().name == "y"
            )),
            "{assigned}"
        );
        assert!(
            effects.iter().any(|effect| matches!(
                effect,
                Effect::If { guard: ControlGuard::DeferredScalar, .. }
            )),
            "{assigned}"
        );
    }
}

#[test]
fn unresolved_function_equality_keeps_both_checked_operands() {
    let source = "function F(a){return a;} template T(){signal input x;F(x)===1;}";
    let result = lift(&[("opaque_equality.circom", source)], Version::new(2, 2, 3));
    let effects = effect_for(&result, "T");
    let Some(Effect::OpaqueEquality { left, right, reason, .. }) = effects.last() else {
        panic!("expected operand-aware opaque equality")
    };
    assert_eq!(*reason, IncompleteReason::UnknownType);
    assert!(matches!(result.hir.expression(*left).unwrap().kind, ExprKind::Call { .. }));
    assert!(matches!(result.hir.expression(*right).unwrap().kind, ExprKind::Number(_)));
}

#[test]
fn array_assertion_is_opaque_but_scalar_assertion_is_checked() {
    let invalid = "template T(){assert([1,2]);}";
    let result = lift(&[("array_assert.circom", invalid)], Version::new(2, 2, 3));
    assert!(effect_for(&result, "T").iter().all(|item| !matches!(item, Effect::Assert { .. })));
    let valid = "template T(){assert(1);}";
    let result = lift(&[("scalar_assert.circom", valid)], Version::new(2, 2, 3));
    assert!(effect_for(&result, "T").iter().any(|item| matches!(item, Effect::Assert { .. })));
}

#[test]
fn function_call_return_shape_is_unknown_until_proven() {
    let cases = [
        "function F(){return [1,2];} template T(){signal output o; o<==F();}",
        "function F(){return 1;} template T(){signal output o; o<==F();}",
    ];
    for source in cases {
        let result = lift(&[("function_shape.circom", source)], Version::new(2, 2, 3));
        assert!(effect_for(&result, "T")
            .iter()
            .all(|item| !matches!(item, Effect::ConstraintAssignment { .. })));
        assert!(result
            .hir
            .expressions()
            .iter()
            .any(|item| { matches!(item.call_target(), Some(CallTarget::Function(_))) }));
    }
}

#[test]
fn bus_argument_does_not_leave_a_checked_function_call() {
    let source =
        concat!("bus B(){signal x;} function F(x){return x;} ", "template T(){B b; var v=F(b);}");
    let result = lift(&[("bus_argument.circom", source)], Version::new(2, 2, 3));
    let start = source.rfind("F(b)").unwrap() + 2;
    assert_eq!(
        diagnostic_fingerprint(&result),
        vec![(SemanticCode::InvalidCallArgument, Severity::Error, 0, start, start + 1)]
    );
    assert!(result
        .hir
        .expressions()
        .iter()
        .any(|item| { matches!(item.call_target(), Some(CallTarget::Opaque { .. })) }));
}
