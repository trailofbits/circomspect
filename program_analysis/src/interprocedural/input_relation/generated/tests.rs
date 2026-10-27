use std::collections::{BTreeMap, BTreeSet};
use std::fs;

use abstract_interpretation::graph::FlowGraph;
use parser::hir::lift_project;
use parser::frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::{build_cfg, CfgNodeKind, Constraint};
use crate::hir_facts::{AnalysisFacts, FactBlocker, GeneratedInputEquation, ProofBudget};
use crate::interprocedural::input_relation::ReadyGeneratedInputs;
use crate::interprocedural::output_enumeration::EnumeratedComponentInstance;
use crate::interprocedural::{CallOwner, CallReachability, ProjectAnalysis, SummaryBlocker};

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
    let provider = ProjectAnalysis::build(&project, Curve::Goldilocks).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &project.hir)
    else {
        return Err(SummaryBlocker::ForeignCall);
    };
    let caller = provider.contexts().main_evidence(&call)?;
    let definition = project.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = provider
        .contexts()
        .analyze_for_evidence(&cfg, &caller, None)
        .map_err(|_| SummaryBlocker::UnsupportedContext)?;
    let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        return Err(SummaryBlocker::ForeignCall);
    };
    let instance = provider.components().enumerate_call(&facts, &caller, &call, 4)?;
    let cfg = build_cfg(&project.hir, call.callee()).unwrap();
    let child = provider
        .contexts()
        .analyze_for_evidence(&cfg, &instance.callee, None)
        .map_err(|_| SummaryBlocker::UnsupportedContext)?;
    let before = facts.no_possible_repeated_body_writes().certified().copied();
    let ready = provider.components().ready_generated_instance(
        &facts,
        &child,
        &instance,
        &mut ProofBudget::default(),
    )?;
    let completed = provider.completed_project_template(&child, &instance.callee, &[])?;
    let completed = provider.completed_generated_child(&facts, &instance, completed, &ready)?;
    provider.completed_generated_template(&facts, &[completed], &ready)?;
    assert_eq!(facts.no_possible_repeated_body_writes().certified().copied(), before);
    let other_curve = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
    assert!(other_curve
        .components()
        .ready_generated_instance(&facts, &child, &instance, &mut ProofBudget::default())
        .is_err());
    let mut equations = Vec::new();
    for (element, binding) in ready.bindings() {
        assert_eq!(element.indices().len(), 1);
        assert_eq!(binding.target, *binding.value.target());
        let local = child.port_handle(element.port(), element.indices()).unwrap();
        let parent = facts
            .component_input_from_local(instance.component, &instance.indices, &local)
            .unwrap();
        let caller_key = facts.component_handle_key(&parent);
        let child_key = child.exact_handle_key(&local);
        assert_eq!(Some(&binding.target), caller_key.certified());
        assert_eq!(ready.ports().input_key(element), child_key.certified());
        assert_eq!(ready.ports().input_element(caller_key.certified().unwrap()), Some(element));
        assert_ne!(caller_key.certified(), child_key.certified());
        assert_eq!(binding.origins.len(), 1);
        let origin = binding.origins[0];
        let mut paired = Vec::new();
        for id in facts.cfg().nodes() {
            let node = facts.cfg().node(*id).unwrap();
            if let CfgNodeKind::Constraint(Constraint::Assignment { target, .. }) = &node.kind {
                let key = facts.exact_closed_component_key(target, *id, ready.ports());
                if node.origin == Some(origin) && key.certified() == Some(&binding.target) {
                    paired.push(*id);
                }
            }
        }
        assert_eq!(paired.len(), 1, "binding retains its generated constraint origin");
        equations.push(binding.value.clone());
    }
    check_refusals(&provider, &facts, &child, &instance, &ready);
    Ok(equations)
}

fn check_refusals(
    provider: &ProjectAnalysis<'_>,
    facts: &AnalysisFacts<'_>,
    child: &AnalysisFacts<'_>,
    instance: &EnumeratedComponentInstance,
    ready: &ReadyGeneratedInputs,
) {
    for budget in
        [ProofBudget::limited(512, 4096, 0, 4096), ProofBudget::limited(512, 4096, 512, 0)]
    {
        let mut budget = budget;
        assert!(provider
            .components()
            .ready_generated_instance(facts, child, instance, &mut budget)
            .is_err());
    }
    let wrong = provider.contexts().symbolic_root(child.definition()).unwrap();
    let wrong = provider.contexts().analyze_for_evidence(child.cfg(), &wrong, None).unwrap();
    assert!(provider
        .components()
        .ready_generated_instance(facts, &wrong, instance, &mut ProofBudget::default())
        .is_err());
    let mut other = instance.clone();
    other.indices.push(0);
    assert!(!ready.matches(facts, &other));
    assert!(provider
        .components()
        .ready_generated_instance(facts, child, &other, &mut ProofBudget::default())
        .is_err());
    let partial =
        provider.contexts().analyze_for_evidence(facts.cfg(), ready.caller(), Some(0)).unwrap();
    assert!(provider
        .components()
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

#[test]
fn generated_input_refusals_preserve_the_first_blocker() {
    for (binding, expected) in [
        ("c.values[0]<==7;", SummaryBlocker::MissingInputBinding),
        ("c.values[0]<==7;c.values[0]<==8;c.values[1]<==9;", SummaryBlocker::DuplicateInputBinding),
        ("c.values[0]<--7;c.values[1]<==8;", SummaryBlocker::WitnessOnlyInput),
        ("c.values[0]<--7;c.values[0]<==9;c.values[1]<==8;", SummaryBlocker::WitnessOnlyInput),
        (
            "signal out;out<--c.out;c.values[0]<==7;c.values[1]<==8;",
            SummaryBlocker::ExternalSummary,
        ),
    ] {
        assert_eq!(inspect(binding, "n").err(), Some(expected), "{binding}");
    }
}

#[test]
fn a_symbolic_input_index_retains_its_expression_blocker() {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-symbolic-readiness-{}-{:?}",
        std::process::id(),
        std::thread::current().id(),
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    let source = "template Child(){signal input values[2];signal output out;out<==values[0];}\
        template Parent(){signal input x;component c=Child();c.values[x]<==7;c.values[1]<==8;}\
        component main=Parent();";
    fs::write(&path, source).unwrap();
    let project = lift_project(&load_sources(
        &[path],
        &[directory],
        VersionPolicy::new(Version::new(2, 2, 3)),
    ));
    let provider = ProjectAnalysis::build(&project, Curve::Goldilocks).unwrap();
    let site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(call) =
        provider.graph().reachable_main_call(site.id(), &project.hir)
    else {
        panic!("main must be reachable");
    };
    let caller = provider.contexts().main_evidence(&call).unwrap();
    let definition = project.hir.definition("Parent").unwrap();
    let cfg = build_cfg(&project.hir, definition).unwrap();
    let facts = provider.contexts().analyze_for_evidence(&cfg, &caller, None).unwrap();
    let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
    let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
    else {
        panic!("child must be reachable");
    };
    let instance = provider.components().enumerate_call(&facts, &caller, &call, 4).unwrap();
    let cfg = build_cfg(&project.hir, call.callee()).unwrap();
    let child = provider.contexts().analyze_for_evidence(&cfg, &instance.callee, None).unwrap();
    let offset = source.find("values[x]").unwrap() + "values[".len();
    let expression = project
        .hir
        .expressions()
        .iter()
        .find(|expression| expression.span.start() == offset && expression.span.end() == offset + 1)
        .unwrap();
    let result = provider.components().ready_generated_instance(
        &facts,
        &child,
        &instance,
        &mut ProofBudget::default(),
    );
    assert_eq!(
        result.err(),
        Some(SummaryBlocker::LocalFacts(BTreeSet::from([FactBlocker::OpaqueExpression(
            expression.id
        ),])))
    );
}
