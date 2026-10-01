use circomspect_program_analysis::hir_facts::FieldContext;
use circomspect_program_analysis::interprocedural::{
    ArgumentShape, ArgumentValue, CallOwner, CallReachability, ContextOrigin, ProjectSummaries,
    SummaryBlocker,
};
use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::analyze;
use parser::hir::{lift_project, LiftedProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
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
fn context_keys_bind_project_curve_version_shape_and_canonical_values() {
    let version = Version::new(2, 2, 3);
    let lifted = fixture("function F(n){return n;} template T(n){}", version);
    let function = lifted.hir.definition("F").unwrap();
    let bn = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let gold = ProjectSummaries::build(&lifted, Curve::Goldilocks).unwrap();
    let bn_field = FieldContext::for_curve(Curve::Bn254);
    let gold_field = FieldContext::for_curve(Curve::Goldilocks);
    let negative = bn
        .context_for(function, vec![ArgumentValue::Scalar(bn_field.canonical((-1).into()))])
        .unwrap();
    let canonical = bn
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
        .context_for(function, vec![ArgumentValue::Scalar(gold_field.canonical((-1).into()))])
        .unwrap();
    assert_ne!(negative, gold_context);
    assert_eq!(gold.check_context(&negative), Err(SummaryBlocker::WrongContext));
    let array = bn.context_for(function, vec![ArgumentValue::Array(vec![])]).unwrap();
    assert_ne!(negative, array);
}

#[test]
fn symbolic_library_context_needs_no_main_and_rejects_foreign_ids() {
    let lifted = fixture("template T(n,m){signal output y;y<==1;}", Version::new(2, 2, 3));
    let foreign = fixture("template T(n,m){}", Version::new(2, 2, 3));
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let context = provider.symbolic_context_for(definition).unwrap();
    assert_eq!(
        context.arguments(),
        [
            ArgumentValue::Symbolic(ArgumentShape::Unknown),
            ArgumentValue::Symbolic(ArgumentShape::Unknown),
        ]
    );
    assert!(lifted.hir.mains().is_empty());
    assert_eq!(
        provider.symbolic_context_for(foreign.hir.definition("T").unwrap()),
        Err(SummaryBlocker::ForeignDefinition)
    );
    assert_eq!(
        provider.context_for(definition, vec![]),
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
    let summaries = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let child = lifted.hir.definition("Child").unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let root = summaries.symbolic_root(child).unwrap();
    assert_eq!(root.origin(), ContextOrigin::SymbolicRoot);
    assert_eq!(root.context().arguments(), [ArgumentValue::Symbolic(ArgumentShape::Unknown)]);

    let main = summaries.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main_call) =
        summaries.graph().reachable_main_call(main.id(), &lifted.hir)
    else {
        panic!("validated main call")
    };
    let main_evidence = summaries.main_evidence(&main_call).unwrap();
    assert_eq!(main_evidence.origin(), ContextOrigin::Main(main.id()));
    assert_eq!(main_evidence.context().definition(), parent);

    let cfg = build_cfg(&lifted.hir, parent).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&lifted.hir, &cfg, &field, None).unwrap();
    let site = summaries.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) = summaries.graph().reachable_call(site.id(), &facts)
    else {
        panic!("reachable child")
    };
    let evidence = summaries.call_evidence(&call, &facts).unwrap();
    assert_eq!(evidence.origin(), ContextOrigin::Call(site.id()));
    assert_eq!(evidence.context().definition(), child);
    assert_eq!(evidence.context().arguments(), [ArgumentValue::Scalar(field.canonical(2.into())),]);
    assert!(summaries.check_evidence(&evidence).is_ok());
    let gold_field = FieldContext::for_curve(Curve::Goldilocks);
    let wrong_curve = analyze(&lifted.hir, &cfg, &gold_field, None).unwrap();
    assert_eq!(summaries.call_evidence(&call, &wrong_curve), Err(SummaryBlocker::ForeignCall));
    let pending = analyze(&lifted.hir, &cfg, &field, Some(0)).unwrap();
    assert!(matches!(summaries.call_evidence(&call, &pending), Err(SummaryBlocker::LocalFacts(_))));
}

#[test]
fn hypothetical_context_does_not_create_a_reachable_scope() {
    let lifted = fixture(
        "template Child(n){} template Parent(){if(0){component dead=Child(2);}}",
        Version::new(2, 2, 3),
    );
    let summaries = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let child = lifted.hir.definition("Child").unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let hypothetical = summaries
        .context_for(child, vec![ArgumentValue::Scalar(field.canonical(2.into()))])
        .unwrap();
    assert!(summaries.check_context(&hypothetical).is_ok());
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
    let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let template = lifted.hir.definition("T").unwrap();
    let parent = lifted.hir.definition("Parent").unwrap();
    let parent_cfg = build_cfg(&lifted.hir, parent).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let parent_facts = analyze(&lifted.hir, &parent_cfg, &field, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_call(site.id(), &parent_facts)
    else {
        panic!("reachable component")
    };
    let one = provider.call_evidence(&call, &parent_facts).unwrap();
    assert_eq!(one.context().definition(), template);
    let cfg = build_cfg(&lifted.hir, template).unwrap();
    let facts_one = provider.analyze_for_evidence(&cfg, &one, None).unwrap();
    assert_eq!(
        provider.analyze_for_evidence(&parent_cfg, &one, None).err(),
        Some(SummaryBlocker::WrongContext)
    );
    let unseeded = analyze(&lifted.hir, &cfg, &field, None).unwrap();
    let root = provider.symbolic_root(template).unwrap();
    let symbolic = provider.analyze_for_evidence(&cfg, &root, None).unwrap();
    assert!(provider.check_facts_for_evidence(&facts_one, &one).is_ok());
    assert_eq!(
        provider.check_facts_for_evidence(&unseeded, &one),
        Err(SummaryBlocker::WrongContext)
    );
    assert_eq!(
        provider.check_facts_for_evidence(&facts_one, &root),
        Err(SummaryBlocker::WrongContext)
    );
    assert!(provider.check_facts_for_evidence(&symbolic, &root).is_ok());
}
