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
use circomspect_program_analysis::hir_facts::{FieldContext, Incidence, Range};
use circomspect_program_analysis::interprocedural::{
    ArgumentValue, FunctionEffect, ProjectSummaries, ReturnEvidence, SummaryBlocker,
    WitnessProvenance,
};
use parser::hir::{lift_project, DefinitionRef, Effect, ExprKind, LiftedProject};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;
use std::fs;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-phase5-summary-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

fn included_fixture(library: &str, root: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-phase5-include-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    fs::write(directory.join("lib.circom"), library).unwrap();
    let path = directory.join("root.circom");
    fs::write(&path, root).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    lift_project(&loaded)
}

#[test]
fn invalid_declaration_dimensions_cannot_certify_function_completion() {
    for declaration in ["var x[-1];", "var x[2][-1];", "var x[0-1];"] {
        let lifted = fixture(&format!(
            "function F(){{{declaration}return 7;}} function Caller(){{var x=F();return 7;}}"
        ));
        assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
        assert!(lifted.syntax_diagnostics.is_empty());
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        for name in ["F", "Caller"] {
            let definition = lifted.hir.definition(name).unwrap();
            let DefinitionRef::Function(function) = definition else { panic!("function") };
            let context = provider.symbolic_context_for(definition).unwrap();
            let summary = provider.function(function, &context);
            assert!(
                summary.certified().and_then(|summary| summary.complete_return()).is_none(),
                "{declaration}: {name}: {summary:?}"
            );
        }
    }
}

#[test]
fn declaration_dimensions_are_checked_in_the_function_context() {
    let lifted = fixture("function F(n){var x[n];return 7;}");
    assert!(lifted.diagnostics.is_empty());
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("F").unwrap();
    let DefinitionRef::Function(function) = definition else { panic!("function") };
    let field = FieldContext::for_curve(Curve::Bn254);
    for argument in [-1, 0, 1, 2] {
        let context = provider
            .context_for(definition, vec![ArgumentValue::Scalar(field.canonical(argument.into()))])
            .unwrap();
        let summary = provider.function(function, &context);
        let result = summary.certified().and_then(|summary| summary.complete_return());
        if argument < 0 {
            assert!(result.is_none(), "{summary:?}");
        } else {
            assert_eq!(result, Some(&Range::Exact(field.canonical(7.into()))));
        }
    }
    let symbolic = provider.symbolic_context_for(definition).unwrap();
    let summary = provider.function(function, &symbolic);
    assert!(summary.certified().and_then(|summary| summary.complete_return()).is_none());
}

#[test]
fn concrete_scalar_function_summary_specializes_return_and_branch() {
    let lifted = fixture("function F(n){if(n){return n+2;}return 2;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(function) = lifted.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let field = FieldContext::for_curve(Curve::Bn254);
    let zero = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Scalar(field.canonical(0.into()))],
        )
        .unwrap();
    let one = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Scalar(field.canonical(1.into()))],
        )
        .unwrap();
    let zero_summary = provider.function(function, &zero);
    let one_summary = provider.function(function, &one);
    assert_eq!(
        zero_summary.certified().unwrap().complete_return().unwrap(),
        &Range::Exact(field.canonical(2.into()))
    );
    assert_eq!(
        one_summary.certified().unwrap().complete_return().unwrap(),
        &Range::Exact(field.canonical(3.into()))
    );
    assert!(provider
        .function(
            function,
            &provider.symbolic_context_for(DefinitionRef::Function(function)).unwrap()
        )
        .unavailable()
        .is_some());
}

#[test]
fn deferred_variable_guard_specializes_for_scalar_but_not_symbolic_argument() {
    let lifted = fixture("function F(n){var x=n;if(x){return 1;}return 2;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(function) = lifted.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let field = FieldContext::for_curve(Curve::Bn254);
    for (argument, expected) in [(0, 2), (1, 1)] {
        let context = provider
            .context_for(
                DefinitionRef::Function(function),
                vec![ArgumentValue::Scalar(field.canonical(argument.into()))],
            )
            .unwrap();
        assert_eq!(
            provider
                .function(function, &context)
                .certified()
                .map(|fact| fact.complete_return().unwrap()),
            Some(&Range::Exact(field.canonical(expected.into())))
        );
    }
    let symbolic = provider.symbolic_context_for(DefinitionRef::Function(function)).unwrap();
    assert!(provider.function(function, &symbolic).unavailable().is_some());
    let array = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Array(vec![ArgumentValue::Scalar(field.canonical(1.into()))])],
        )
        .unwrap();
    assert!(provider
        .function(function, &array)
        .unavailable()
        .unwrap()
        .iter()
        .any(|blocker| matches!(blocker, SummaryBlocker::InvalidAssignment(_))));
}

#[test]
fn deferred_assignment_is_checked_even_when_later_overwritten() {
    let lifted = fixture("function F(n){var x=n;x=1;return x;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(function) = lifted.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let field = FieldContext::for_curve(Curve::Bn254);
    let array = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Array(vec![ArgumentValue::Scalar(field.canonical(0.into()))])],
        )
        .unwrap();
    assert!(provider
        .function(function, &array)
        .unavailable()
        .unwrap()
        .iter()
        .any(|blocker| matches!(blocker, SummaryBlocker::InvalidAssignment(_))));
    let scalar = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Scalar(field.canonical(0.into()))],
        )
        .unwrap();
    assert_eq!(
        provider.function(function, &scalar).certified().unwrap().complete_return().unwrap(),
        &Range::Exact(field.canonical(1.into()))
    );
}

#[test]
fn unused_array_argument_does_not_block_a_constant_return() {
    let lifted = fixture("function F(n){return 7;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(function) = lifted.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let field = FieldContext::for_curve(Curve::Bn254);
    let context = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Array(vec![ArgumentValue::Scalar(field.canonical(1.into()))])],
        )
        .unwrap();
    assert_eq!(
        provider.function(function, &context).certified().unwrap().complete_return().unwrap(),
        &Range::Exact(field.canonical(7.into()))
    );
}

#[test]
fn constant_return_survives_an_unrelated_opaque_call() {
    for (source, expected) in [
        ("function F(){var t=Missing();return 7;}", Some(7)),
        ("function F(){var t=Missing();return t;}", None),
        ("function F(n){if(n+Missing()){return 1;}return 7;}", None),
    ] {
        let lifted = fixture(source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let DefinitionRef::Function(function) = lifted.hir.definition("F").unwrap() else {
            panic!("F must be a function")
        };
        let context = provider.symbolic_context_for(DefinitionRef::Function(function)).unwrap();
        let summary = provider.function(function, &context);
        let field = FieldContext::for_curve(Curve::Bn254);
        match expected {
            Some(value) => {
                let expected = Range::Exact(field.canonical(value.into()));
                assert_eq!(
                    summary.certified().unwrap().return_evidence(),
                    ReturnEvidence::Conditional(&expected)
                );
            }
            None => assert!(summary.unavailable().is_some()),
        }
    }
}

#[test]
fn a_constant_value_after_an_opaque_call_is_conditional() {
    let lifted = fixture("function F(){var t=Missing();return 7;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else { panic!("F") };
    let context = provider.symbolic_context_for(DefinitionRef::Function(f)).unwrap();
    let summary = provider.function(f, &context);
    let expected = Range::Exact(FieldContext::for_curve(Curve::Bn254).canonical(7.into()));
    assert_eq!(
        summary.certified().unwrap().return_evidence(),
        ReturnEvidence::Conditional(&expected)
    );
}

#[test]
fn a_failing_assertion_cannot_certify_a_later_return() {
    let lifted = fixture("function F(){assert(0);return 7;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else { panic!("F") };
    let context = provider.symbolic_context_for(DefinitionRef::Function(f)).unwrap();
    let summary = provider.function(f, &context);
    assert!(summary.certified().and_then(|value| value.complete_return()).is_none());
}

#[test]
fn assertion_coverage_uses_the_bound_context_and_reachable_branch() {
    let lifted = fixture(
        "function F(n){if(n){assert(n);}return 7;} \
         function G(n){if(n){assert(0);}return 7;}",
    );
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else { panic!("F") };
    let DefinitionRef::Function(g) = lifted.hir.definition("G").unwrap() else { panic!("G") };
    let field = FieldContext::for_curve(Curve::Bn254);
    for (function, value, complete) in [(f, 0, true), (f, 1, true), (g, 0, true), (g, 1, false)] {
        let context = provider
            .context_for(
                DefinitionRef::Function(function),
                vec![ArgumentValue::Scalar(field.canonical(value.into()))],
            )
            .unwrap();
        let summary = provider.function(function, &context);
        assert_eq!(
            summary.certified().and_then(|item| item.complete_return()).is_some(),
            complete,
            "{function:?}({value}): {:?}",
            summary.unavailable()
        );
    }
    let symbolic = provider.symbolic_context_for(DefinitionRef::Function(f)).unwrap();
    assert!(provider
        .function(f, &symbolic)
        .certified()
        .and_then(|item| item.complete_return())
        .is_none());
}

#[test]
fn checked_true_assertion_retains_complete_return_evidence() {
    let lifted = fixture("function F(){assert(1);return 7;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else { panic!("F") };
    let context = provider.symbolic_context_for(DefinitionRef::Function(f)).unwrap();
    let summary = provider.function(f, &context);
    let expected = Range::Exact(FieldContext::for_curve(Curve::Bn254).canonical(7.into()));
    assert_eq!(summary.certified().and_then(|item| item.complete_return()), Some(&expected));
}

#[test]
fn opaque_assertion_effect_cannot_certify_a_later_return() {
    let lifted = fixture("function F(){assert([1,2]);return 7;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else { panic!("F") };
    let context = provider.symbolic_context_for(DefinitionRef::Function(f)).unwrap();
    let summary = provider.function(f, &context);
    assert!(summary.certified().and_then(|item| item.complete_return()).is_none());
}

#[test]
fn division_by_zero_before_return_does_not_certify_completion() {
    for (denominator, complete) in [(0, false), (1, true)] {
        let lifted = fixture(&format!("function F(){{var x=1/{denominator};return 7;}}"));
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else { panic!("F") };
        let context = provider.symbolic_context_for(DefinitionRef::Function(f)).unwrap();
        let summary = provider.function(f, &context);
        assert_eq!(
            summary.certified().and_then(|item| item.complete_return()).is_some(),
            complete,
            "denominator {denominator}: {:?}",
            summary.unavailable()
        );
    }
}

#[test]
fn compound_assignments_cannot_borrow_plain_assignment_return_facts() {
    let cases = [
        ("function F(){var x=1;x/=0;return 7;}", false),
        ("function F(){var x=1;x+=1;return x;}", false),
        ("function F(){var x=1;return x;}", true),
    ];
    for (source, complete) in cases {
        let lifted = fixture(source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else { panic!("F") };
        let context = provider.symbolic_context_for(DefinitionRef::Function(f)).unwrap();
        let summary = provider.function(f, &context);
        let exact_one = Range::Exact(FieldContext::for_curve(Curve::Bn254).canonical(1.into()));
        assert_eq!(
            summary.certified().and_then(|item| item.complete_return()),
            if complete { Some(&exact_one) } else { None },
            "{source}: {:?}",
            summary.unavailable()
        );
    }
}

#[test]
fn indexed_reads_and_writes_need_proved_bounds_before_complete_return() {
    let cases = [
        ("function F(){var x[1]=[1];var t=x[1];return 7;}", false),
        ("function F(){var x[1]=[1];x[1]=2;return 7;}", false),
        ("function F(){var x[1]=[1];var t=x[0];return 7;}", true),
        ("function F(){var x[1]=[1];x[0]=2;return 7;}", true),
        ("function F(){var x[1]=[1];var i=0;var t=x[i];return 7;}", true),
        ("function F(){var x[1]=[1];var i=1;var t=x[i];return 7;}", false),
        ("function F(){var x[1]=[1];var t=x[-1];return 7;}", false),
        ("function F(){var x[2]=[0,1];var t=x[x[2]];return 7;}", false),
        ("function F(){var x[1]=[1];x[1]++;return 7;}", false),
        ("function F(){var x[1]=[1];x[0]++;return 7;}", false),
        ("function F(){var x[2][1]=[[1],[2]];var t=x[0][1];return 7;}", false),
        ("function F(){var x[2][1]=[[1],[2]];var t=x[1][0];return 7;}", true),
    ];
    let expected = Range::Exact(FieldContext::for_curve(Curve::Bn254).canonical(7.into()));
    for (source, complete) in cases {
        let lifted = fixture(source);
        assert!(lifted.diagnostics.is_empty(), "{source}: {:?}", lifted.diagnostics);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else { panic!("F") };
        let context = provider.symbolic_context_for(DefinitionRef::Function(f)).unwrap();
        let summary = provider.function(f, &context);
        assert_eq!(
            summary.certified().and_then(|item| item.complete_return()),
            if complete { Some(&expected) } else { None },
            "{source}: {:?}",
            summary.unavailable()
        );
    }
}

#[test]
fn indexed_bounds_follow_the_bound_parameter_context() {
    let lifted = fixture("function F(n){var x[n];x[0]=1;return 7;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else { panic!("F") };
    let field = FieldContext::for_curve(Curve::Bn254);
    let expected = Range::Exact(field.canonical(7.into()));
    for (size, complete) in [(0, false), (1, true), (2, true)] {
        let context = provider
            .context_for(
                DefinitionRef::Function(f),
                vec![ArgumentValue::Scalar(field.canonical(size.into()))],
            )
            .unwrap();
        let summary = provider.function(f, &context);
        assert_eq!(
            summary.certified().and_then(|item| item.complete_return()),
            if complete { Some(&expected) } else { None },
            "F({size}): {:?}",
            summary.unavailable()
        );
    }
    let symbolic = provider.symbolic_context_for(DefinitionRef::Function(f)).unwrap();
    let summary = provider.function(f, &symbolic);
    assert!(summary.certified().and_then(|item| item.complete_return()).is_none());
}

#[test]
fn conditional_return_coverage_propagates_through_a_direct_call() {
    let field = FieldContext::for_curve(Curve::Bn254);
    let lifted = fixture("function G(){var t=Missing();return 7;} function F(){return G();}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else { panic!("F") };
    let context = provider.symbolic_context_for(DefinitionRef::Function(f)).unwrap();
    let summary = provider.function(f, &context);
    let expected = Range::Exact(field.canonical(7.into()));
    assert_eq!(
        summary.certified().unwrap().return_evidence(),
        ReturnEvidence::Conditional(&expected)
    );
}

#[test]
fn a_structural_fallthrough_path_cannot_supply_complete_return_evidence() {
    let lifted = fixture("function F(n){if(n){return 7;}}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else { panic!("F") };
    let field = FieldContext::for_curve(Curve::Bn254);
    let one = provider
        .context_for(
            DefinitionRef::Function(f),
            vec![ArgumentValue::Scalar(field.canonical(1.into()))],
        )
        .unwrap();
    let summary = provider.function(f, &one);
    let expected = Range::Exact(field.canonical(7.into()));
    assert_eq!(
        summary.certified().unwrap().return_evidence(),
        ReturnEvidence::Conditional(&expected)
    );
    let symbolic = provider.symbolic_context_for(DefinitionRef::Function(f)).unwrap();
    let symbolic_summary = provider.function(f, &symbolic);
    if let Some(summary) = symbolic_summary.certified() {
        let ReturnEvidence::Conditional(_) = summary.return_evidence() else {
            panic!("symbolic fallthrough cannot prove a complete return")
        };
    }
}

#[test]
fn foreign_and_non_scalar_contexts_never_certify_function_returns() {
    let lifted = fixture("function F(n){return n;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(function) = lifted.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let array = provider
        .context_for(DefinitionRef::Function(function), vec![ArgumentValue::Array(vec![])])
        .unwrap();
    assert!(provider.function(function, &array).unavailable().is_some());
    let other = fixture("function F(n){return 1;}");
    let DefinitionRef::Function(foreign) = other.hir.definition("F").unwrap() else {
        panic!("foreign function F")
    };
    assert_eq!(
        provider.function(foreign, &array).unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::ForeignDefinition]))
    );
}

#[test]
fn symbolic_library_root_certifies_a_parameter_independent_return() {
    let lifted = fixture("function F(n){return 7;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(function) = lifted.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let context = provider.symbolic_context_for(DefinitionRef::Function(function)).unwrap();
    let summary = provider.function(function, &context);
    let field = FieldContext::for_curve(Curve::Bn254);
    assert_eq!(
        summary.certified().unwrap().complete_return().unwrap(),
        &Range::Exact(field.canonical(7.into()))
    );
    assert!(summary.certified().unwrap().input_dependencies().is_empty());
}

#[test]
fn scalar_context_cannot_validate_an_indexed_parameter_use() {
    let lifted = fixture("function F(n){return n[0];}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(function) = lifted.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let field = FieldContext::for_curve(Curve::Bn254);
    let context = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Scalar(field.canonical(1.into()))],
        )
        .unwrap();
    assert!(provider.function(function, &context).unavailable().is_some());
}

#[test]
fn direct_resolved_function_call_agrees_with_inlined_return() {
    let lifted = fixture("function Id(a){return a;} function Outer(n){return Id(n);}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(outer) = lifted.hir.definition("Outer").unwrap() else {
        panic!("function Outer")
    };
    let body = lifted.hir.block(lifted.hir.function(outer).unwrap().body).unwrap();
    let Some(Effect::Return { value, .. }) = body.effects.first() else { panic!("Outer return") };
    let expression = lifted.hir.expression(*value).unwrap();
    assert!(matches!(expression.kind, ExprKind::Call { .. }), "{:?}", expression.kind);
    let field = FieldContext::for_curve(Curve::Bn254);
    let context = provider
        .context_for(
            DefinitionRef::Function(outer),
            vec![ArgumentValue::Scalar(field.canonical(5.into()))],
        )
        .unwrap();
    let summary = provider.function(outer, &context);
    assert_eq!(
        summary.certified().unwrap().complete_return().unwrap(),
        &Range::Exact(field.canonical(5.into()))
    );
    assert_eq!(
        summary.certified().unwrap().input_dependencies(),
        &std::collections::BTreeSet::from([0])
    );
}

#[test]
fn included_function_summary_composes_across_source_files() {
    let lifted = included_fixture(
        "function Id(a){return a;}",
        "include \"lib.circom\"; function Outer(n){return Id(n);}",
    );
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(outer) = lifted.hir.definition("Outer").unwrap() else {
        panic!("Outer")
    };
    let field = FieldContext::for_curve(Curve::Bn254);
    let context = provider
        .context_for(
            DefinitionRef::Function(outer),
            vec![ArgumentValue::Scalar(field.canonical(9.into()))],
        )
        .unwrap();
    assert_eq!(
        provider.function(outer, &context).certified().unwrap().complete_return().unwrap(),
        &Range::Exact(field.canonical(9.into()))
    );
}

#[test]
fn finite_recursive_contexts_reach_a_base_case_without_certifying_a_cycle() {
    let lifted = fixture("function F(n){if(n){return F(n-1);}return 0;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(function) = lifted.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let field = FieldContext::for_curve(Curve::Bn254);
    let concrete = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Scalar(field.canonical(3.into()))],
        )
        .unwrap();
    let summary = provider.function(function, &concrete);
    assert_eq!(
        summary.certified().map(|item| item.complete_return().unwrap()),
        Some(&Range::Exact(field.canonical(0.into()))),
        "{:?}",
        summary.unavailable()
    );
    let too_deep = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Scalar(field.canonical(70.into()))],
        )
        .unwrap();
    assert_eq!(
        provider.function(function, &too_deep).unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::ContextBudget]))
    );
    assert_eq!(
        provider.function(function, &too_deep).unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::ContextBudget]))
    );

    let cyclic = fixture("function F(n){return F(n);}");
    let cyclic_provider = ProjectSummaries::build(&cyclic, Curve::Bn254).unwrap();
    let DefinitionRef::Function(cyclic_id) = cyclic.hir.definition("F").unwrap() else {
        panic!("cyclic F")
    };
    let context = cyclic_provider
        .context_for(
            DefinitionRef::Function(cyclic_id),
            vec![ArgumentValue::Scalar(field.canonical(1.into()))],
        )
        .unwrap();
    assert_eq!(
        cyclic_provider.function(cyclic_id, &context).unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::RecursiveCycle]))
    );
}

#[test]
fn mutual_recursion_with_repeated_context_abstains_from_return_value() {
    let lifted = fixture(
        "function F(n){if(n){return G(n);}return 7;} \
         function G(n){if(n){return F(n);}return 7;}",
    );
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let DefinitionRef::Function(g) = lifted.hir.definition("G").unwrap() else {
        panic!("function G")
    };
    let field = FieldContext::for_curve(Curve::Bn254);
    let zero = ArgumentValue::Scalar(field.canonical(0.into()));
    let one = ArgumentValue::Scalar(field.canonical(1.into()));
    let base = provider.context_for(DefinitionRef::Function(f), vec![zero]).unwrap();
    let cycle = provider.context_for(DefinitionRef::Function(f), vec![one.clone()]).unwrap();
    let g_cycle = provider.context_for(DefinitionRef::Function(g), vec![one]).unwrap();

    assert_eq!(
        provider.function(f, &base).certified().and_then(|summary| summary.complete_return()),
        Some(&Range::Exact(field.canonical(7.into())))
    );
    // Repeating the same immutable argument tuple proves no terminating return path.
    for (function, context) in [(f, cycle), (g, g_cycle)] {
        assert_eq!(
            provider.function(function, &context).unavailable(),
            Some(&std::collections::BTreeSet::from([SummaryBlocker::RecursiveCycle]))
        );
    }
}

#[test]
fn mutually_recursive_concrete_contexts_reach_the_same_base_return() {
    let lifted = fixture(
        "function F(n){if(n){return G(n-1);}return 0;} \
         function G(n){if(n){return F(n-1);}return 0;}",
    );
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else { panic!("F") };
    let DefinitionRef::Function(g) = lifted.hir.definition("G").unwrap() else { panic!("G") };
    let field = FieldContext::for_curve(Curve::Bn254);
    for (function, value) in [(f, 4), (g, 3)] {
        let context = provider
            .context_for(
                DefinitionRef::Function(function),
                vec![ArgumentValue::Scalar(field.canonical(value.into()))],
            )
            .unwrap();
        let summary = provider.function(function, &context);
        assert_eq!(
            summary.certified().map(|item| item.complete_return().unwrap()),
            Some(&Range::Exact(field.canonical(0.into()))),
            "{value}: {:?}",
            summary.unavailable()
        );
    }
    let symbolic = provider.symbolic_context_for(DefinitionRef::Function(f)).unwrap();
    assert!(provider.function(f, &symbolic).unavailable().is_some());
}

#[test]
fn a_self_call_before_a_constant_return_cannot_certify_termination() {
    let lifted = fixture("function F(){var ignored=F();return 7;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else { panic!("F") };
    let context = provider.symbolic_context_for(DefinitionRef::Function(f)).unwrap();
    assert!(provider.function(f, &context).unavailable().is_some());
}

#[test]
fn recursive_scc_effects_reach_a_least_fixed_point() {
    let lifted = fixture(
        "function F(n){if(n){return G(n);}return 0;} \
         function G(n){log(n);if(n){return F(n);}return 0;}",
    );
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else { panic!("F") };
    let DefinitionRef::Function(g) = lifted.hir.definition("G").unwrap() else { panic!("G") };
    let field = FieldContext::for_curve(Curve::Bn254);
    let one = ArgumentValue::Scalar(field.canonical(1.into()));
    let f_one = provider.context_for(DefinitionRef::Function(f), vec![one.clone()]).unwrap();
    let g_one = provider.context_for(DefinitionRef::Function(g), vec![one]).unwrap();
    assert!(provider
        .function_effects(f, &f_one)
        .certified()
        .unwrap()
        .contains(FunctionEffect::Log));
    assert!(provider
        .function_effects(g, &g_one)
        .certified()
        .unwrap()
        .contains(FunctionEffect::Log));
    assert_eq!(
        provider.function(f, &f_one).unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::RecursiveCycle]))
    );
    let f_zero = provider
        .context_for(
            DefinitionRef::Function(f),
            vec![ArgumentValue::Scalar(field.canonical(0.into()))],
        )
        .unwrap();
    assert!(!provider
        .function_effects(f, &f_zero)
        .certified()
        .unwrap()
        .contains(FunctionEffect::Log));
}

#[test]
fn unreachable_and_unrelated_opaque_calls_do_not_invent_effects() {
    let lifted = fixture(
        "function G(){log(1);return 1;} \
         function Clean(){if(0){return G();}return 1;} \
         function Broken(){return Missing();}",
    );
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(clean) = lifted.hir.definition("Clean").unwrap() else {
        panic!("Clean")
    };
    let DefinitionRef::Function(broken) = lifted.hir.definition("Broken").unwrap() else {
        panic!("Broken")
    };
    let clean_context = provider.symbolic_context_for(DefinitionRef::Function(clean)).unwrap();
    let broken_context = provider.symbolic_context_for(DefinitionRef::Function(broken)).unwrap();
    let clean_effects = provider.function_effects(clean, &clean_context);
    assert!(!clean_effects.certified().unwrap().contains(FunctionEffect::Log));
    assert!(provider.function_effects(broken, &broken_context).unavailable().is_some());
    assert!(provider.function_effects(broken, &broken_context).unavailable().is_some());
    assert_eq!(
        provider.function(clean, &clean_context).certified().unwrap().complete_return().unwrap(),
        &Range::Exact(FieldContext::for_curve(Curve::Bn254).canonical(1.into()))
    );
}

#[test]
fn template_port_summary_specializes_constraint_provenance() {
    let lifted = fixture("template T(n){signal output x;if(n){x<==1;}else{x<--1;}}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Template(template) = lifted.hir.definition("T").unwrap() else {
        panic!("template T")
    };
    let port = lifted.hir.template(template).unwrap().ports[0];
    let field = FieldContext::for_curve(Curve::Bn254);
    let one = provider
        .context_for(
            DefinitionRef::Template(template),
            vec![ArgumentValue::Scalar(field.canonical(1.into()))],
        )
        .unwrap();
    let zero = provider
        .context_for(
            DefinitionRef::Template(template),
            vec![ArgumentValue::Scalar(field.canonical(0.into()))],
        )
        .unwrap();
    let symbolic = provider.symbolic_context_for(DefinitionRef::Template(template)).unwrap();
    let constrained = provider.template_port(template, &one, port);
    assert_eq!(constrained.certified().unwrap().incidence(), Incidence::Must);
    assert_eq!(constrained.certified().unwrap().fixed_value(), Some(&field.canonical(1.into())));
    assert_eq!(
        provider.template_port(template, &zero, port).certified().unwrap().incidence(),
        Incidence::Zero
    );
    assert!(provider.template_port(template, &symbolic, port).unavailable().is_some());
    assert!(lifted.hir.mains().is_empty());
}

#[test]
fn complete_call_result_through_local_access_agrees_with_inlining() {
    let field = FieldContext::for_curve(Curve::Bn254);
    for value in ["7", "F()"] {
        let source = format!(
            "function F(){{return 7;}} template T(){{var x={value};signal output out;out<==x;}}"
        );
        let lifted = fixture(&source);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let DefinitionRef::Template(template) = lifted.hir.definition("T").unwrap() else {
            panic!("template T")
        };
        let port = lifted.hir.template(template).unwrap().ports[0];
        let context = provider.symbolic_context_for(DefinitionRef::Template(template)).unwrap();
        let summary = provider.template_port(template, &context, port);
        let summary = summary.certified().expect("complete call result");
        assert_eq!(summary.incidence(), Incidence::Must, "{value}");
        assert_eq!(summary.fixed_value(), Some(&field.canonical(7.into())), "{value}");
    }
}

#[test]
fn deferred_variable_guard_specializes_template_constraint_incidence() {
    let lifted = fixture("template T(n){var x=n;signal output y;if(x){y<==1;}else{y<--1;}}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Template(template) = lifted.hir.definition("T").unwrap() else {
        panic!("template T")
    };
    let port = lifted.hir.template(template).unwrap().ports[0];
    let field = FieldContext::for_curve(Curve::Bn254);
    for (argument, incidence) in [(0, Incidence::Zero), (1, Incidence::Must)] {
        let context = provider
            .context_for(
                DefinitionRef::Template(template),
                vec![ArgumentValue::Scalar(field.canonical(argument.into()))],
            )
            .unwrap();
        assert_eq!(
            provider.template_port(template, &context, port).certified().unwrap().incidence(),
            incidence
        );
    }
    let symbolic = provider.symbolic_context_for(DefinitionRef::Template(template)).unwrap();
    assert!(provider.template_port(template, &symbolic, port).unavailable().is_some());
}

#[test]
fn template_port_summary_keeps_witness_and_read_evidence_separate() {
    let lifted = fixture("template T(){signal input x;signal output y,z;y<--x;z<==1;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Template(template) = lifted.hir.definition("T").unwrap() else {
        panic!("template T")
    };
    let ports = &lifted.hir.template(template).unwrap().ports;
    let context = provider.symbolic_context_for(DefinitionRef::Template(template)).unwrap();
    assert_eq!(provider.template_port_read(template, &context, ports[0]).certified(), Some(&true));
    assert_eq!(
        provider.template_port_witnesses(template, &context, ports[1]).certified().map(Vec::len),
        Some(1)
    );
    assert_eq!(
        provider.template_port_witnesses(template, &context, ports[1]).certified().unwrap()[0]
            .provenance(),
        WitnessProvenance::WitnessOnly
    );
    assert_eq!(
        provider.template_port(template, &context, ports[1]).certified().unwrap().incidence(),
        Incidence::Zero
    );
    assert_eq!(
        provider.template_port_witnesses(template, &context, ports[2]).certified().map(Vec::len),
        Some(1)
    );
    assert_eq!(
        provider.template_port_witnesses(template, &context, ports[2]).certified().unwrap()[0]
            .provenance(),
        WitnessProvenance::GeneratedConstraint
    );
    assert_eq!(
        provider.template_port(template, &context, ports[2]).certified().unwrap().incidence(),
        Incidence::Must
    );
}

#[test]
fn opaque_witness_write_cannot_certify_an_empty_witness_summary() {
    let lifted = fixture("template T(){signal output y;y<--Missing();}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Template(template) = lifted.hir.definition("T").unwrap() else {
        panic!("template T")
    };
    let port = lifted.hir.template(template).unwrap().ports[0];
    let context = provider.symbolic_context_for(DefinitionRef::Template(template)).unwrap();
    assert!(provider.template_port_witnesses(template, &context, port).unavailable().is_some());
    assert!(provider.template_port_witnesses(template, &context, port).unavailable().is_some());
}

#[test]
fn exact_array_port_summaries_retain_distinct_element_identity() {
    let lifted = fixture("template T(){signal output out[2];out[0]<==1;out[1]<--2;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Template(template) = lifted.hir.definition("T").unwrap() else {
        panic!("template T")
    };
    let port = lifted.hir.template(template).unwrap().ports[0];
    let context = provider.symbolic_context_for(DefinitionRef::Template(template)).unwrap();
    let first = provider.template_port_at(template, &context, port, &[0]);
    let second = provider.template_port_at(template, &context, port, &[1]);
    assert_eq!(first.certified().unwrap().indices(), [0]);
    assert_eq!(second.certified().unwrap().indices(), [1]);
    assert_eq!(first.certified().unwrap().incidence(), Incidence::Must);
    assert_eq!(second.certified().unwrap().incidence(), Incidence::Zero);
    assert_eq!(provider.template_port_at(template, &context, port, &[0]), first);
    assert_eq!(provider.template_port_at(template, &context, port, &[1]), second);
    let other_curve = ProjectSummaries::build(&lifted, Curve::Goldilocks).unwrap();
    let foreign_context =
        other_curve.symbolic_context_for(DefinitionRef::Template(template)).unwrap();
    assert_eq!(
        provider.template_port_at(template, &foreign_context, port, &[0]).unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::WrongContext]))
    );
}

#[test]
fn cached_function_families_keep_concrete_and_symbolic_contexts_separate() {
    let lifted = fixture("function F(n){if(n){log(n);}return n;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(function) = lifted.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let field = FieldContext::for_curve(Curve::Bn254);
    let zero = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Scalar(field.canonical(0.into()))],
        )
        .unwrap();
    let one = provider
        .context_for(
            DefinitionRef::Function(function),
            vec![ArgumentValue::Scalar(field.canonical(1.into()))],
        )
        .unwrap();
    for context in [&one, &zero, &one] {
        let expected = context.arguments()[0].clone();
        let ArgumentValue::Scalar(expected) = expected else { panic!("scalar context") };
        assert_eq!(
            provider.function(function, context).certified().unwrap().complete_return(),
            Some(&Range::Exact(expected.clone()))
        );
        assert_eq!(
            provider
                .function_effects(function, context)
                .certified()
                .unwrap()
                .contains(FunctionEffect::Log),
            expected == field.canonical(1.into())
        );
    }
    let symbolic = provider.symbolic_context_for(DefinitionRef::Function(function)).unwrap();
    assert!(provider.function(function, &symbolic).unavailable().is_some());
    assert!(provider.function(function, &symbolic).unavailable().is_some());
    assert_eq!(
        provider.function(function, &one).certified().unwrap().complete_return(),
        Some(&Range::Exact(field.canonical(1.into())))
    );
}

#[test]
fn cached_queries_reject_foreign_curve_version_and_project_contexts() {
    let lifted = fixture("function F(){return -1;}");
    let bn = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let goldilocks = ProjectSummaries::build(&lifted, Curve::Goldilocks).unwrap();
    let DefinitionRef::Function(function) = lifted.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let definition = DefinitionRef::Function(function);
    let bn_context = bn.context_for(definition, vec![]).unwrap();
    let goldilocks_context = goldilocks.context_for(definition, vec![]).unwrap();
    assert_ne!(bn_context, goldilocks_context);
    let bn_return = bn.function(function, &bn_context);
    let goldilocks_return = goldilocks.function(function, &goldilocks_context);
    assert_ne!(
        bn_return.certified().unwrap().complete_return(),
        goldilocks_return.certified().unwrap().complete_return()
    );
    assert_eq!(
        bn.function(function, &goldilocks_context).unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::WrongContext]))
    );
    assert_eq!(
        bn.function_effects(function, &goldilocks_context).unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::WrongContext]))
    );

    let mut changed_version = lifted.clone();
    changed_version.version = Version::new(2, 1, 0);
    let older = ProjectSummaries::build(&changed_version, Curve::Bn254).unwrap();
    let older_context = older.context_for(definition, vec![]).unwrap();
    assert_ne!(bn_context, older_context);
    assert_eq!(
        bn.function(function, &older_context).unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::WrongContext]))
    );

    let foreign_lifted = fixture("function F(){return -1;}");
    let foreign = ProjectSummaries::build(&foreign_lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(foreign_id) = foreign_lifted.hir.definition("F").unwrap() else {
        panic!("foreign F")
    };
    let foreign_context = foreign.context_for(DefinitionRef::Function(foreign_id), vec![]).unwrap();
    assert_eq!(
        bn.function(function, &foreign_context).unavailable(),
        Some(&std::collections::BTreeSet::from([SummaryBlocker::WrongContext]))
    );
}

#[test]
fn complete_call_result_agrees_with_inlined_template_constraint() {
    let lifted = fixture(
        "function F(){return 7;} \
         template Inline(){signal output out;out<==7;} \
         template Called(){signal output out;out<==F();}",
    );
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    for name in ["Inline", "Called"] {
        let DefinitionRef::Template(template) = lifted.hir.definition(name).unwrap() else {
            panic!("template")
        };
        let port = lifted.hir.template(template).unwrap().ports[0];
        let context = provider.symbolic_context_for(DefinitionRef::Template(template)).unwrap();
        let summary = provider.template_port(template, &context, port);
        assert_eq!(
            summary
                .certified()
                .map(circomspect_program_analysis::interprocedural::PortSummary::incidence),
            Some(Incidence::Must)
        );
        assert_eq!(
            summary.certified().and_then(|item| item.fixed_value()),
            Some(&field.canonical(7.into()))
        );
    }
}

#[test]
fn complete_call_result_flows_through_a_local_variable() {
    let lifted = fixture(
        "function F(){return 7;} \
         function Inline(){var t=7;return t;} \
         function Called(){var t=F();return t;}",
    );
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let expected = Range::Exact(FieldContext::for_curve(Curve::Bn254).canonical(7.into()));
    for name in ["Inline", "Called"] {
        let DefinitionRef::Function(function) = lifted.hir.definition(name).unwrap() else {
            panic!("function")
        };
        let context = provider.symbolic_context_for(DefinitionRef::Function(function)).unwrap();
        let summary = provider.function(function, &context);
        assert_eq!(
            summary.certified().and_then(|item| item.complete_return()),
            Some(&expected),
            "{name}: {summary:?}"
        );
    }
}

#[test]
fn specialized_call_retains_its_return_argument_dependency() {
    let lifted = fixture("function Id(a){return a;} function G(n){var t=Id(n);return t;}");
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(g) = lifted.hir.definition("G").unwrap() else {
        panic!("function G")
    };
    let field = FieldContext::for_curve(Curve::Bn254);
    let context = provider
        .context_for(
            DefinitionRef::Function(g),
            vec![ArgumentValue::Scalar(field.canonical(5.into()))],
        )
        .unwrap();
    let summary = provider.function(g, &context);
    let summary = summary.certified().unwrap();
    assert_eq!(summary.complete_return(), Some(&Range::Exact(field.canonical(5.into()))));
    assert_eq!(summary.input_dependencies(), &std::collections::BTreeSet::from([0]));
}

#[test]
fn deferred_assertion_uses_the_concrete_scalar_context() {
    let lifted = fixture(
        "function F(n){assert(n);return 7;} \
         template T(n){signal output out;out<==F(n);}",
    );
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let DefinitionRef::Function(f) = lifted.hir.definition("F").unwrap() else {
        panic!("function F")
    };
    let DefinitionRef::Template(t) = lifted.hir.definition("T").unwrap() else {
        panic!("template T")
    };
    let output = lifted.hir.template(t).unwrap().ports[0];
    let field = FieldContext::for_curve(Curve::Bn254);
    let one = ArgumentValue::Scalar(field.canonical(1.into()));
    let zero = ArgumentValue::Scalar(field.canonical(0.into()));
    let negative_one = ArgumentValue::Scalar(field.canonical((-1).into()));
    let prime = ArgumentValue::Scalar(
        field
            .parse("21888242871839275222246405745257275088548364400416034343698204186575808495617")
            .unwrap(),
    );
    let f_one = provider.context_for(DefinitionRef::Function(f), vec![one.clone()]).unwrap();
    let f_zero = provider.context_for(DefinitionRef::Function(f), vec![zero.clone()]).unwrap();
    assert_eq!(
        provider.function(f, &f_one).certified().and_then(|item| item.complete_return()),
        Some(&Range::Exact(field.canonical(7.into())))
    );
    assert!(provider
        .function(f, &f_zero)
        .certified()
        .and_then(|item| item.complete_return())
        .is_none());
    let f_negative_one =
        provider.context_for(DefinitionRef::Function(f), vec![negative_one]).unwrap();
    assert_eq!(
        provider.function(f, &f_negative_one).certified().and_then(|item| item.complete_return()),
        Some(&Range::Exact(field.canonical(7.into())))
    );
    let f_prime = provider.context_for(DefinitionRef::Function(f), vec![prime]).unwrap();
    assert!(provider
        .function(f, &f_prime)
        .certified()
        .and_then(|item| item.complete_return())
        .is_none());
    let f_array = provider
        .context_for(
            DefinitionRef::Function(f),
            vec![ArgumentValue::Array(vec![ArgumentValue::Scalar(field.canonical(1.into()))])],
        )
        .unwrap();
    assert!(provider
        .function(f, &f_array)
        .certified()
        .and_then(|item| item.complete_return())
        .is_none());
    let t_one = provider.context_for(DefinitionRef::Template(t), vec![one]).unwrap();
    let t_zero = provider.context_for(DefinitionRef::Template(t), vec![zero]).unwrap();
    let one_output = provider.template_port(t, &t_one, output);
    assert_eq!(
        one_output.certified().and_then(|item| item.fixed_value()),
        Some(&field.canonical(7.into()))
    );
    assert!(provider.template_port(t, &t_zero, output).certified().is_none());
    let symbolic = provider.symbolic_context_for(DefinitionRef::Function(f)).unwrap();
    assert!(provider
        .function(f, &symbolic)
        .certified()
        .and_then(|item| item.complete_return())
        .is_none());
}
