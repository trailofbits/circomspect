use std::collections::BTreeMap;
use std::fs;

use parser::hir::lift_project;
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::build_cfg;
use crate::hir_facts::{AnalysisFacts, GeneratedInputEquation, ProofBudget};
use crate::interprocedural::input_relation::ReadyGeneratedInputs;
use crate::interprocedural::output_enumeration::EnumeratedComponentInstance;
use crate::interprocedural::{CallOwner, CallReachability, ProjectSummaries, SummaryBlocker};

fn inspect(binding: &str, dimension: &str) -> Result<Vec<GeneratedInputEquation>, SummaryBlocker> {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-generated-readiness-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(
        &path,
        format!(
            "template Child(n){{signal input values[{dimension}];signal output out;\
        out<==values[0]+values[1];}}\
        template Parent(){{signal input x;component c=Child(2);{binding}}}\
        component main=Parent();"
        ),
    )
    .unwrap();
    let project = lift_project(&load_sources(
        &[path],
        &[directory],
        VersionPolicy::new(Version::new(2, 2, 3)),
    ));
    let provider = ProjectSummaries::build(&project, Curve::Goldilocks).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &project.hir)
    else {
        return Err(SummaryBlocker::ForeignCall);
    };
    let caller = provider.main_evidence(&call)?;
    let definition = project.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = provider
        .analyze_for_evidence(&cfg, &caller, None)
        .map_err(|_| SummaryBlocker::UnsupportedContext)?;
    let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        return Err(SummaryBlocker::ForeignCall);
    };
    let instance = provider.enumerate_call(&facts, &caller, &call, 4)?;
    let cfg = build_cfg(&project.hir, call.callee()).unwrap();
    let child = provider
        .analyze_for_evidence(&cfg, &instance.callee, None)
        .map_err(|_| SummaryBlocker::UnsupportedContext)?;
    let before = facts.no_possible_repeated_body_writes().certified().copied();
    let ready = provider.ready_generated_instance(
        &facts,
        &child,
        &instance,
        &mut ProofBudget::default(),
    )?;
    let completed = provider.completed_project_template(&child, &instance.callee, &[])?;
    let completed = provider.completed_generated_child(&facts, &instance, completed, &ready)?;
    provider.completed_generated_template(&facts, &[completed], &ready)?;
    assert_eq!(facts.no_possible_repeated_body_writes().certified().copied(), before);
    let other_curve = ProjectSummaries::build(&project, Curve::Bn254).unwrap();
    assert!(other_curve
        .ready_generated_instance(&facts, &child, &instance, &mut ProofBudget::default())
        .is_err());
    let mut equations = Vec::new();
    for (element, binding) in ready.bindings() {
        assert_eq!(element.indices().len(), 1);
        assert_eq!(binding.target, *binding.value.target());
        assert!(ready.ports().input_key(element).is_some());
        equations.push(binding.value.clone());
    }
    check_refusals(&provider, &facts, &child, &instance, &ready);
    Ok(equations)
}

fn check_refusals(
    provider: &ProjectSummaries<'_>,
    facts: &AnalysisFacts<'_>,
    child: &AnalysisFacts<'_>,
    instance: &EnumeratedComponentInstance,
    ready: &ReadyGeneratedInputs,
) {
    for budget in
        [ProofBudget::limited(512, 4096, 0, 4096), ProofBudget::limited(512, 4096, 512, 0)]
    {
        let mut budget = budget;
        assert!(provider.ready_generated_instance(facts, child, instance, &mut budget).is_err());
    }
    let wrong = provider.symbolic_root(child.definition()).unwrap();
    let wrong = provider.analyze_for_evidence(child.cfg(), &wrong, None).unwrap();
    assert!(provider
        .ready_generated_instance(facts, &wrong, instance, &mut ProofBudget::default())
        .is_err());
    let mut other = instance.clone();
    other.indices.push(0);
    assert!(!ready.matches(facts, &other));
    assert!(provider
        .ready_generated_instance(facts, child, &other, &mut ProofBudget::default())
        .is_err());
    let partial = provider.analyze_for_evidence(facts.cfg(), ready.caller(), Some(0)).unwrap();
    assert!(provider
        .ready_generated_instance(&partial, child, instance, &mut ProofBudget::default())
        .is_err());
}

#[test]
fn generated_array_inputs_keep_exact_cells_and_affine_constraint_provenance() {
    for dimension in ["2", "n"] {
        let equations = inspect("c.values[0]<==7;c.values[1]<==x+3;", dimension).unwrap();
        assert_eq!(equations.len(), 2);
        assert_ne!(equations[0].target(), equations[1].target());
        let field = crate::hir_facts::FieldContext::for_curve(Curve::Goldilocks);
        let mut assignment = BTreeMap::new();
        for key in equations[1].equation().accesses() {
            assignment.insert(key.clone(), field.canonical(9.into()));
        }
        let value = equations[1]
            .equation()
            .solve_linear_target(&field, &assignment, equations[1].target())
            .unwrap()
            .unwrap();
        assert_eq!(value.as_bigint().to_string(), "12");
    }
}

#[test]
fn specialized_loop_indices_bind_distinct_array_cells_at_their_own_sites() {
    let equations = inspect("for(var i=0;i<2;i++){c.values[i]<==i+7;}", "n").unwrap();
    let field = crate::hir_facts::FieldContext::for_curve(Curve::Goldilocks);
    let values: Vec<_> = equations
        .iter()
        .map(|equation| {
            equation
                .equation()
                .singleton_solution(&field)
                .unwrap()
                .unwrap()
                .1
                .as_bigint()
                .to_string()
        })
        .collect();
    assert_eq!(values, ["7", "8"]);
}

#[test]
fn generated_array_readiness_rejects_incomplete_opaque_and_witness_bindings() {
    for binding in [
        "c.values[0]<==7;",
        "c.values[0]<==7;c.values[0]<==8;c.values[1]<==9;",
        "c.values[0]<--7;c.values[1]<==8;",
        "c.values[0]<==7;c.values[2]<==8;",
        "c.values[x]<==7;c.values[1]<==8;",
        "signal out;out<--c.out;c.values[0]<==7;c.values[1]<==8;",
        "signal local;c.values[0]<==local;c.values[1]<==8;",
        "c.values[0]<==7;c.values[1]<==8;assert(0);",
        "c.values[0]<==7;c.values[1]<==8;var bad=1/0;",
        "if(x){c.values[0]<==7;}c.values[1]<==8;",
        "signal input a;signal input b;signal input d;c.values[0]<==a*b+x*d;c.values[1]<==8;",
    ] {
        assert!(inspect(binding, "n").is_err(), "{binding}");
    }
}
