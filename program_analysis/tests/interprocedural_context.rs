use circomspect_program_analysis::hir_facts::FieldContext;
use circomspect_program_analysis::interprocedural::{
    ArgumentShape, ArgumentValue, ProjectSummaries, SummaryBlocker,
};
use parser::hir::{lower_project, LoweredProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;
use std::fs;

fn fixture(source: &str, version: Version) -> LoweredProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-phase5-context-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(version));
    lower_project(&loaded)
}

#[test]
fn context_keys_bind_project_curve_version_shape_and_canonical_values() {
    let version = Version::new(2, 2, 3);
    let lowered = fixture("function F(n){return n;} template T(n){}", version);
    let function = lowered.hir.definition("F").unwrap();
    let bn = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let gold = ProjectSummaries::build(&lowered, Curve::Goldilocks).unwrap();
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
    let lowered = fixture("template T(n,m){signal output y;y<==1;}", Version::new(2, 2, 3));
    let foreign = fixture("template T(n,m){}", Version::new(2, 2, 3));
    let provider = ProjectSummaries::build(&lowered, Curve::Bn254).unwrap();
    let definition = lowered.hir.definition("T").unwrap();
    let context = provider.symbolic_context_for(definition).unwrap();
    assert_eq!(
        context.arguments(),
        [
            ArgumentValue::Symbolic(ArgumentShape::Unknown),
            ArgumentValue::Symbolic(ArgumentShape::Unknown),
        ]
    );
    assert!(lowered.hir.mains().is_empty());
    assert_eq!(
        provider.symbolic_context_for(foreign.hir.definition("T").unwrap()),
        Err(SummaryBlocker::ForeignDefinition)
    );
    assert_eq!(
        provider.context_for(definition, vec![]),
        Err(SummaryBlocker::WrongArity { expected: 2, actual: 0 })
    );
}
