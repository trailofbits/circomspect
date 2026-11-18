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
use abstract_interpretation::graph::FlowGraph;
use circomspect_program_analysis::hir_facts::{FieldContext, Range};
use circomspect_program_analysis::interprocedural::{
    AnalyzeEvidenceError, ArgumentShape, ArgumentValue, CallOwner, CallReachability, ContextOrigin,
    ProjectAnalysis, SummaryBlocker,
};
use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::analyze;
use parser::hir::{lift_project, ExprKind, LiftedProject, SemanticCode, Severity};
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;
use std::fs;

fn fixture(source: &str, version: Version) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-phase5-context-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(version));
    lift_project(&loaded)
}

#[test]
fn parameter_writes_cannot_certify_the_stale_incoming_value() {
    for (statement, expected) in [("n=1;", 1), ("n+=1;", 3), ("n++;", 3)] {
        let source = format!("template T(n){{{statement}var x=n;}} component main=T(2);");
        let lifted = fixture(&source, Version::new(2, 2, 3));
        assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
        let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let site = summaries.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            summaries.graph().reachable_main_call(site.id(), &lifted.hir)
        else {
            panic!("main T(2) is reachable")
        };
        let evidence = summaries.contexts().main_evidence(&call).unwrap();
        let cfg = build_cfg(&lifted.hir, evidence.context().definition()).unwrap();
        let facts = summaries.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let mut observed = false;
        for expression in lifted.hir.expressions() {
            let ExprKind::Access(path) = &expression.kind else { continue };
            if lifted.hir.symbol(path.root).unwrap().name != "n" {
                continue;
            }
            observed = true;
            if let Some(Range::Exact(value)) = facts.range(expression.id).certified() {
                let field = FieldContext::for_curve(Curve::Bn254);
                assert_eq!(*value, field.canonical(expected.into()), "{statement}");
            }
        }
        assert!(observed);
    }
}

#[test]
fn context_curve_labels_and_order_are_stable() {
    let lifted = fixture("function F(){return 7;}", Version::new(2, 2, 3));
    assert!(lifted.diagnostics.is_empty());
    let definition = lifted.hir.definition("F").unwrap();
    let [bn, bls, gold] = [Curve::Bn254, Curve::Bls12_381, Curve::Goldilocks].map(|curve| {
        let analysis = ProjectAnalysis::build(&lifted, curve).unwrap();
        analysis.contexts().context_for(definition, vec![]).unwrap()
    });
    assert!(format!("{bn:?}").contains("curve: Bn254,"));
    assert!(format!("{bls:?}").contains("curve: Bls12_381,"));
    assert!(format!("{gold:?}").contains("curve: Goldilocks,"));
    assert!(bn < bls);
    assert!(bls < gold);
    assert!(bn < gold);
}

#[test]
fn context_keys_bind_project_curve_version_shape_and_canonical_values() {
    let version = Version::new(2, 2, 3);
    let lifted = fixture("function F(n){return n;} template T(n){}", version);
    let function = lifted.hir.definition("F").unwrap();
    let bn = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let gold = ProjectAnalysis::build(&lifted, Curve::Goldilocks).unwrap();
    let bn_field = FieldContext::for_curve(Curve::Bn254);
    let gold_field = FieldContext::for_curve(Curve::Goldilocks);
    let negative = bn
        .contexts()
        .context_for(function, vec![ArgumentValue::Scalar(bn_field.canonical((-1).into()))])
        .unwrap();
    let canonical = bn.contexts()
        .context_for(
            function,
            vec![ArgumentValue::Scalar(
                bn_field.parse("21888242871839275222246405745257275088548364400416034343698204186575808495616").unwrap(),
            )],
        )
        .unwrap();
    assert_eq!(negative, canonical);
    assert_eq!(negative.version(), version);
    let gold_context = gold
        .contexts()
        .context_for(function, vec![ArgumentValue::Scalar(gold_field.canonical((-1).into()))])
        .unwrap();
    assert_ne!(negative, gold_context);
    assert_eq!(gold.contexts().check_context(&negative), Err(SummaryBlocker::WrongContext));
    let array = bn.contexts().context_for(function, vec![ArgumentValue::Array(vec![])]).unwrap();
    assert_ne!(negative, array);
}

#[test]
fn symbolic_library_context_needs_no_main_and_rejects_foreign_ids() {
    let lifted = fixture("template T(n,m){signal output y;y<==1;}", Version::new(2, 2, 3));
    let foreign = fixture("template T(n,m){}", Version::new(2, 2, 3));
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let context = provider.contexts().symbolic_context_for(definition).unwrap();
    assert_eq!(
        context.arguments(),
        [
            ArgumentValue::Symbolic(ArgumentShape::Unknown),
            ArgumentValue::Symbolic(ArgumentShape::Unknown),
        ]
    );
    assert!(lifted.hir.mains().is_empty());
    assert_eq!(
        provider.contexts().symbolic_context_for(foreign.hir.definition("T").unwrap()),
        Err(SummaryBlocker::ForeignDefinition)
    );
    assert_eq!(
        provider.contexts().context_for(definition, vec![]),
        Err(SummaryBlocker::WrongArity { expected: 2, actual: 0 })
    );
}

#[test]
fn evidence_scope_distinguishes_universal_root_from_a_reachable_call() {
    let lifted = fixture(
        "template Child(n){} template Parent(){component c=Child(2);} \
         component main=Parent();",
        Version::new(2, 2, 3),
    );
    let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let child = lifted.hir.definition("Child").unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let root = summaries.contexts().symbolic_root(child).unwrap();
    assert_eq!(root.origin(), ContextOrigin::SymbolicRoot);
    assert_eq!(root.context().arguments(), [ArgumentValue::Symbolic(ArgumentShape::Unknown)]);

    let main = summaries.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main_call) =
        summaries.graph().reachable_main_call(main.id(), &lifted.hir)
    else {
        panic!("validated main call")
    };
    let main_evidence = summaries.contexts().main_evidence(&main_call).unwrap();
    assert_eq!(main_evidence.origin(), ContextOrigin::Main(main.id()));
    assert_eq!(main_evidence.context().definition(), parent);

    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = summaries.contexts().analyze_for_evidence(&cfg, &main_evidence, None).unwrap();
    let site = summaries.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = summaries.graph().reachable_call(site.id(), &facts)
    else {
        panic!("reachable child")
    };
    let evidence = summaries.contexts().call_evidence(&call, &facts, &main_evidence).unwrap();
    assert_eq!(evidence.origin(), ContextOrigin::Call(site.id()));
    assert_eq!(evidence.context().definition(), child);
    assert_eq!(evidence.context().arguments(), [ArgumentValue::Scalar(field.canonical(2.into())),]);
    assert!(summaries.contexts().check_evidence(&evidence).is_ok());
    let gold_field = FieldContext::for_curve(Curve::Goldilocks);
    let wrong_curve = analyze(&lifted.hir, &cfg, &gold_field, None).unwrap();
    assert_eq!(
        summaries.contexts().call_evidence(&call, &wrong_curve, &main_evidence),
        Err(SummaryBlocker::ForeignCall)
    );
    let pending = summaries.contexts().analyze_for_evidence(&cfg, &main_evidence, Some(0)).unwrap();
    assert!(matches!(
        summaries.contexts().call_evidence(&call, &pending, &main_evidence),
        Err(SummaryBlocker::LocalFacts(_))
    ));
}

#[test]
fn unbound_local_facts_cannot_mint_reachable_child_evidence() {
    let lifted = fixture(
        "template Child(n){} template Parent(){component c=Child(2);}",
        Version::new(2, 2, 3),
    );
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let unbound = analyze(&lifted.hir, &cfg, &field, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &unbound)
    else {
        panic!("checked call must be reachable")
    };
    let caller = provider.contexts().symbolic_root(parent).unwrap();
    assert_eq!(
        provider.contexts().call_evidence(&call, &unbound, &caller),
        Err(SummaryBlocker::WrongContext)
    );
}

#[test]
fn specializing_two_calls_keeps_one_source_diagnostic_for_a_missing_callee() {
    let lifted = fixture(
        concat!(
            "template Child(n){var t=Missing(n);signal output out;out<==1;} ",
            "template Parent(){component c[2];c[0]=Child(0);c[1]=Child(1);}",
            "component main=Parent();"
        ),
        Version::new(2, 2, 3),
    );
    let missing = || {
        lifted
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == SemanticCode::MissingCall)
            .count()
    };
    assert_eq!(missing(), 1);
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let child = lifted.hir.definition("Child").unwrap();
    let main_site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main) =
        provider.graph().reachable_main_call(main_site.id(), &lifted.hir)
    else {
        panic!("main must resolve")
    };
    let root = provider.contexts().main_evidence(&main).unwrap();
    let parent_cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&parent_cfg, &root, None).unwrap();
    let child_cfg = build_cfg(&lifted.hir, child).unwrap();
    let sites = provider.graph().calls_from(CallOwner::Definition(parent));
    let mut contexts = Vec::new();
    for site in sites {
        let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
        else {
            panic!("child call must be reachable")
        };
        let evidence = provider.contexts().call_evidence(&call, &facts, &root).unwrap();
        provider.contexts().analyze_for_evidence(&child_cfg, &evidence, None).unwrap();
        contexts.push(evidence.context().clone());
    }
    assert_ne!(contexts[0], contexts[1]);
    assert_eq!(missing(), 1);
}

#[test]
fn reachable_array_call_preserves_shape_and_emits_a_located_assignment_error() {
    let source = concat!(
        "template Child(n){var x=n;x=1;signal output out;out<==1;} ",
        "template Parent(){component c=Child([1,2]);} component main=Parent();"
    );
    let lifted = fixture(source, Version::new(2, 2, 3));
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let child = lifted.hir.definition("Child").unwrap();
    let parent_cfg = build_cfg(&lifted.hir, parent).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main_call) =
        provider.graph().reachable_main_call(main.id(), provider.hir())
    else {
        panic!("main call must be reachable")
    };
    let caller = provider.contexts().main_evidence(&main_call).unwrap();
    let parent_facts =
        provider.contexts().analyze_for_evidence(&parent_cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_call(site.id(), &parent_facts)
    else {
        panic!("array call must be reachable")
    };
    let evidence = provider.contexts().call_evidence(&call, &parent_facts, &caller).unwrap();
    assert_eq!(
        evidence.context().arguments(),
        [ArgumentValue::Array(vec![
            ArgumentValue::Scalar(field.canonical(1.into())),
            ArgumentValue::Scalar(field.canonical(2.into())),
        ])]
    );
    let child_cfg = build_cfg(&lifted.hir, child).unwrap();
    let error =
        provider.contexts().analyze_for_evidence(&child_cfg, &evidence, None).err().unwrap();
    let AnalyzeEvidenceError::InvalidAssignment { context, diagnostic } = error else {
        panic!("aggregate argument must make the deferred scalar write invalid")
    };
    assert_eq!(*context, *evidence.context());
    assert_eq!(diagnostic.code, SemanticCode::InvalidAssignment);
    assert_eq!(diagnostic.code.as_str(), "T2000");
    assert_eq!(diagnostic.severity, Severity::Error);
    assert_eq!(&source[diagnostic.span.start()..diagnostic.span.end()], "n");
}

#[test]
fn scalar_main_specializes_deferred_guard_while_symbolic_library_scope_abstains() {
    let lifted = fixture(
        "template T(n){var x=n;signal output y;if(x){y<==1;}else{y<==2;}} \
         component main=T(0);",
        Version::new(2, 2, 3),
    );
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let parser::hir::DefinitionRef::Template(template) = definition else {
        panic!("T must be a template")
    };
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let output = lifted.hir.template(template).unwrap().ports[0];
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(main.id(), provider.hir())
    else {
        panic!("main call must be reachable")
    };
    let concrete = provider.contexts().main_evidence(&call).unwrap();
    let concrete_facts = provider.contexts().analyze_for_evidence(&cfg, &concrete, None).unwrap();
    let concrete_handle = concrete_facts.port_handle(output, &[]).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    assert_eq!(
        concrete_facts.constraint_fixed_handle(&concrete_handle).certified(),
        Some(&Some(field.canonical(2.into())))
    );

    let symbolic = provider.contexts().symbolic_root(definition).unwrap();
    let symbolic_facts = provider.contexts().analyze_for_evidence(&cfg, &symbolic, None).unwrap();
    let symbolic_handle = symbolic_facts.port_handle(output, &[]).unwrap();
    assert!(symbolic_facts.constraint_fixed_handle(&symbolic_handle).unavailable().is_some());
}

#[test]
fn aggregate_argument_in_dead_arm_or_call_argument_is_not_a_scalar_assignment_error() {
    for source in [
        "template T(n){var x=0?n:1;signal output y;y<==1;} component main=T([1,2]);",
        "function First(a){return a[0];} template T(n){var x=First(n);signal output y;\
         y<==1;} component main=T([1,2]);",
        "template T(n){var c=n[0];var x=c?n:1;signal output y;y<==1;} \
         component main=T([1,2]);",
    ] {
        let lifted = fixture(source, Version::new(2, 2, 3));
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("T").unwrap();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let site = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph().reachable_main_call(site.id(), provider.hir())
        else {
            panic!("main call must be reachable")
        };
        let evidence = provider.contexts().main_evidence(&call).unwrap();
        let result = provider.contexts().analyze_for_evidence(&cfg, &evidence, None);
        assert!(!matches!(result, Err(AnalyzeEvidenceError::InvalidAssignment { .. })));
    }
}

#[test]
fn concrete_taken_branch_rejects_a_scalar_assignment_from_an_array() {
    let lifted = fixture(
        "template T(n){var x=1;if(1){x=n;}signal output y;y<==x;} \
         component main=T([1,2]);",
        Version::new(2, 2, 3),
    );
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let parser::hir::DefinitionRef::Template(template) = definition else {
        panic!("T must be a template")
    };
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), provider.hir())
    else {
        panic!("main call must be reachable")
    };
    let evidence = provider.contexts().main_evidence(&call).unwrap();
    let error = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).err().unwrap();
    let AnalyzeEvidenceError::InvalidAssignment { diagnostic, .. } = error else {
        panic!("the taken scalar assignment is invalid")
    };
    assert_eq!(diagnostic.code, SemanticCode::InvalidAssignment);
    let output = lifted.hir.template(template).unwrap().ports[0];
    assert!(provider
        .templates()
        .template_port(template, evidence.context(), output)
        .certified()
        .is_none());
}

#[test]
fn hypothetical_context_does_not_create_a_reachable_scope() {
    let lifted = fixture(
        "template Child(n){} template Parent(){if(0){component dead=Child(2);}}",
        Version::new(2, 2, 3),
    );
    let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let child = lifted.hir.definition("Child").unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let hypothetical = summaries
        .contexts()
        .context_for(child, vec![ArgumentValue::Scalar(field.canonical(2.into()))])
        .unwrap();
    assert!(summaries.contexts().check_context(&hypothetical).is_ok());
    let parent = lifted.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let facts = analyze(&lifted.hir, &cfg, &field, None).unwrap();
    let site = summaries.graph().calls_from(CallOwner::Definition(parent))[0];
    assert!(matches!(
        summaries.graph().reachable_call(site.id(), &facts),
        CallReachability::Unreachable
    ));
}

#[test]
fn local_facts_must_match_the_exact_evidence_scope() {
    let lifted = fixture(
        "template T(n){signal output y;if(n){y<==1;}else{y<--1;}} \
         template Parent(){component a=T(1);} component main=Parent();",
        Version::new(2, 2, 3),
    );
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let template = lifted.hir.definition("T").unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let parent_cfg = build_cfg(&lifted.hir, parent).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let main = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main_call) =
        provider.graph().reachable_main_call(main.id(), provider.hir())
    else {
        panic!("main call must be reachable")
    };
    let caller = provider.contexts().main_evidence(&main_call).unwrap();
    let parent_facts =
        provider.contexts().analyze_for_evidence(&parent_cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_call(site.id(), &parent_facts)
    else {
        panic!("reachable component")
    };
    let one = provider.contexts().call_evidence(&call, &parent_facts, &caller).unwrap();
    assert_eq!(one.context().definition(), template);
    let cfg = build_cfg(&lifted.hir, template).unwrap();
    let facts_one = provider.contexts().analyze_for_evidence(&cfg, &one, None).unwrap();
    assert_eq!(
        provider.contexts().analyze_for_evidence(&parent_cfg, &one, None).err(),
        Some(circomspect_program_analysis::interprocedural::AnalyzeEvidenceError::Blocked(
            SummaryBlocker::WrongContext,
        ))
    );
    let unseeded = analyze(&lifted.hir, &cfg, &field, None).unwrap();
    let root = provider.contexts().symbolic_root(template).unwrap();
    let symbolic = provider.contexts().analyze_for_evidence(&cfg, &root, None).unwrap();
    assert!(provider.contexts().check_facts_for_evidence(&facts_one, &one).is_ok());
    assert_eq!(
        provider.contexts().check_facts_for_evidence(&unseeded, &one),
        Err(SummaryBlocker::WrongContext)
    );
    assert_eq!(
        provider.contexts().check_facts_for_evidence(&facts_one, &root),
        Err(SummaryBlocker::WrongContext)
    );
    assert!(provider.contexts().check_facts_for_evidence(&symbolic, &root).is_ok());
}

fn parameter_operation_error(source: &str) -> Option<AnalyzeEvidenceError> {
    let lifted = fixture(source, Version::new(2, 2, 3));
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), provider.hir())
    else {
        panic!("main must be reachable")
    };
    let evidence = provider.contexts().main_evidence(&call).unwrap();
    let cfg = build_cfg(provider.hir(), evidence.context().definition()).unwrap();
    provider.contexts().analyze_for_evidence(&cfg, &evidence, None).err()
}

#[test]
fn parameter_shape_errors_are_located_in_the_reachable_main_context() {
    for (statement, argument, code, location) in [
        ("var x=n[0];", "1", SemanticCode::InvalidArrayAccess, "n[0]"),
        ("n[1]=1;", "[2]", SemanticCode::InvalidArrayAccess, "n[1]"),
        ("n[0][1]=1;", "[[2]]", SemanticCode::InvalidArrayAccess, "n[0][1]"),
        ("n=1;", "[2]", SemanticCode::InvalidAssignment, "n"),
        ("n=[1];", "2", SemanticCode::InvalidAssignment, "n"),
        ("n+=1;", "[2]", SemanticCode::InvalidAssignment, "n"),
        ("n++;", "[2]", SemanticCode::InvalidAssignment, "n"),
    ] {
        let source = format!("template T(n){{{statement}}} component main=T({argument});");
        let error = parameter_operation_error(&source).expect("invalid concrete parameter use");
        let diagnostic = error.diagnostic().expect("a located semantic diagnostic");
        assert_eq!(diagnostic.code, code, "{source}");
        assert_eq!(&source[diagnostic.span.start()..diagnostic.span.end()], location);
    }
}

#[test]
fn parameter_shape_validation_preserves_valid_and_unexecuted_operations() {
    for (statement, argument) in [
        ("n=1;", "2"),
        ("n=[1];", "[2]"),
        ("n=[1,2];", "[2]"),
        ("var x[1];x=n;", "[2]"),
        ("var x[1][1];x[0]=n;", "[2]"),
        ("n[0]=1;", "[2]"),
        ("n[0][0]=1;", "[[2]]"),
        ("if(0){n[1]=1;}", "[2]"),
        ("if(1){n[0]=1;}else{n[1]=1;}", "[2]"),
    ] {
        let source = format!("template T(n){{{statement}}} component main=T({argument});");
        assert!(parameter_operation_error(&source).is_none(), "{source}");
    }
}

#[test]
fn unrolled_scalar_checks_preserve_a_later_invalid_parameter_use() {
    let source = concat!(
        "template T(n){var sum=0;for(var i=0;i<64;i++){sum+=i+1;}",
        "var bad=n[0];}component main=T(3);"
    );
    let error = parameter_operation_error(source).expect("invalid scalar argument index");
    let diagnostic = error.diagnostic().expect("located parameter error");
    assert_eq!(diagnostic.code, SemanticCode::InvalidArrayAccess);
    assert_eq!(&source[diagnostic.span.start()..diagnostic.span.end()], "n[0]");
}

#[test]
fn unrolled_scalar_checks_do_not_certify_a_budget_limited_range() {
    let source = concat!(
        "template T(n){var sum=0;for(var i=0;i<16;i++){sum+=i+1;}}",
        "component main=T(3);"
    );
    let lifted = fixture(source, Version::new(2, 2, 3));
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), provider.hir())
    else {
        panic!("main must be reachable")
    };
    let evidence = provider.contexts().main_evidence(&call).unwrap();
    let cfg = build_cfg(provider.hir(), evidence.context().definition()).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, Some(0)).unwrap();
    let expression = lifted
        .hir
        .expressions()
        .iter()
        .find(|expression| &source[expression.span.start()..expression.span.end()] == "i+1")
        .unwrap();
    assert!(facts.range(expression.id).unavailable().is_some());
}

#[test]
fn public_cfg_queries_follow_the_specialized_control_flow() {
    let source = concat!(
        "function F(){return 7;} ",
        "template T(){signal output out;out<==F();var x;",
        "if(0){x=1;}else{x=2;}} component main=T();"
    );
    let lifted = fixture(source, Version::new(2, 2, 3));
    let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), provider.hir())
    else {
        panic!("main must be reachable")
    };
    let evidence = provider.contexts().main_evidence(&call).unwrap();
    let cfg = build_cfg(provider.hir(), evidence.context().definition()).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let mut branches = 0;
    for id in facts.cfg().edges() {
        let edge = facts.cfg().edge(*id).unwrap();
        let expected = match edge.payload.kind {
            circomspect_program_analysis::hir_cfg::EdgeKind::True => false,
            circomspect_program_analysis::hir_cfg::EdgeKind::False => true,
            circomspect_program_analysis::hir_cfg::EdgeKind::Normal
            | circomspect_program_analysis::hir_cfg::EdgeKind::Loop
            | circomspect_program_analysis::hir_cfg::EdgeKind::Return => continue,
        };
        branches += 1;
        assert_eq!(facts.reachable_edge(*id).certified(), Some(&expected));
    }
    assert_eq!(branches, 2);
}

#[test]
fn original_bounds_nested_shapes_and_index_values() {
    for (statement, argument, invalid) in [
        ("n=[1,2];var x=n[1];", "[2]", true),
        ("n=[[1,2]];var x=n[0][1];", "[[2]]", true),
        ("n=[[1,2]];var x=n[0][0];", "[[2]]", false),
        ("n[0]=[1];", "[[2]]", false),
        ("n[0]=1;", "[[2]]", true),
        ("n[0]++;", "[[2]]", true),
        ("n[0]+=1;", "[[2]]", true),
        ("n[0][0]+=1;", "[[2]]", false),
        ("var i=0;i++;n[i]=1;", "[2]", true),
        ("var i=1;i--;n[i]=1;", "[2]", false),
        ("var i=0;n[i-1]=1;", "[2]", true),
        ("if(0){n[0]=1;}", "1", false),
        ("if(1){n[0]=1;}", "1", true),
        ("var x=1?n[0]:7;", "1", true),
        ("var x=0?n[0]:7;", "1", false),
    ] {
        let source = format!("template T(n){{{statement}}} component main=T({argument});");
        assert_eq!(parameter_operation_error(&source).is_some(), invalid, "{source}");
    }
}

#[test]
fn optional_bad_access_cannot_become_a_definite_error_at_low_budget() {
    for body in ["if(c){n[0]=1;}", "while(c){n[0]=1;}", "var x=c?n[0]:7;"] {
        let source = format!("template T(n){{signal input c;{body}}} component main=T(1);");
        let lifted = fixture(&source, Version::new(2, 2, 3));
        assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let site = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph().reachable_main_call(site.id(), provider.hir())
        else {
            panic!("main call must be reachable")
        };
        let evidence = provider.contexts().main_evidence(&call).unwrap();
        let cfg = build_cfg(provider.hir(), evidence.context().definition()).unwrap();
        for budget in 0..100 {
            let result = provider.contexts().analyze_for_evidence(&cfg, &evidence, Some(budget));
            assert!(result.is_ok(), "budget {budget}, {source}: {:?}", result.err());
        }
    }
}

#[test]
fn fallthrough_value_effects_do_not_prune_unknown_control_or_indices() {
    for body in [
        "n=[1,2];if(c){n[1]=1;}",
        "n=[1,2];while(c){n[1]=1;}",
        "n=[1,2];var x=c?n[1]:7;",
        "var i=1;if(c){i=0;}n=[1,2];n[i]=1;",
        "var i=1;while(c){i=0;}n=[1,2];n[i]=1;",
        "n=[1,2];if(0){n[1]=1;}",
    ] {
        let source = format!("template T(n){{signal input c;{body}}} component main=T([2]);");
        let lifted = fixture(&source, Version::new(2, 2, 3));
        assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let site = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph().reachable_main_call(site.id(), provider.hir())
        else {
            panic!("main call must be reachable")
        };
        let evidence = provider.contexts().main_evidence(&call).unwrap();
        let cfg = build_cfg(provider.hir(), evidence.context().definition()).unwrap();
        for budget in 0..128 {
            let result = provider.contexts().analyze_for_evidence(&cfg, &evidence, Some(budget));
            assert!(result.is_ok(), "budget {budget}, {source}: {:?}", result.err());
        }
    }
}

#[test]
fn temporary_context_views_preserve_fact_borrows() {
    let lifted = fixture("template T(){signal output y;y<==7;}", Version::new(2, 2, 3));
    let analysis = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = analysis.contexts().symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let expression = lifted
        .hir
        .expressions()
        .iter()
        .find(|expression| {
            let ExprKind::Number(value) = &expression.kind else { return false };
            value == "7"
        })
        .unwrap()
        .id;
    let first = analysis.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let second = {
        let queries = analysis.contexts();
        queries.analyze_for_evidence(&cfg, &evidence, None).unwrap()
    };
    let field = FieldContext::for_curve(Curve::Bn254);
    assert_eq!(first.range(expression).certified(), Some(&Range::Exact(field.canonical(7.into()))));
    assert_eq!(second.range(expression), first.range(expression));
}
