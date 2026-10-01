use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::{analyze, FactBlocker, FieldContext, Incidence};
use circomspect_program_analysis::interprocedural::{
    build_call_graph, CallOwner, CallProvenance, CallReachability,
};
use parser::hir::{lift_project, CallTarget, DefinitionRef, HirProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;
use std::fs;

fn fixture(sources: &[(&str, &str)]) -> HirProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-phase5-graph-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let mut roots = Vec::new();
    for (name, source) in sources {
        let path = directory.join(name);
        fs::write(&path, source).unwrap();
        roots.push(path);
    }
    let loaded = load_sources(&roots, &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    lifted.hir
}

#[test]
fn graph_finds_assignment_guard_nested_and_index_calls_without_main() {
    let hir = fixture(&[
        ("lib.circom", "function Leaf(a){return a;} function Guard(a){return a;}"),
        (
            "use.circom",
            "function Outer(n){var x=Leaf(n);if(Guard(n)){return Leaf(x);}return 0;} \
             template Check(){signal output y[2];y[Leaf(0)]<==1;}",
        ),
    ]);
    let graph = build_call_graph(&hir).unwrap();
    let outer = hir.definition("Outer").unwrap();
    let check = hir.definition("Check").unwrap();
    let outer_calls = graph.calls_from(CallOwner::Definition(outer));
    assert_eq!(outer_calls.len(), 3);
    assert!(outer_calls.iter().all(|site| matches!(site.target, CallTarget::Function(_))));
    let index_calls = graph.calls_from(CallOwner::Definition(check));
    assert_eq!(index_calls.len(), 1);
    assert!(matches!(index_calls[0].target, CallTarget::Function(_)));
    assert_eq!(index_calls[0].provenance, CallProvenance::Unattached);
    assert!(index_calls[0].resolved().is_some());
    assert!(hir.mains().is_empty());
}

#[test]
fn graph_records_component_anonymous_and_main_edges_by_resolved_id() {
    let hir = fixture(&[(
        "components.circom",
        "template Child(){signal input in;signal output out;out<==in;} \
         template Check(){component c=Child();signal output y;y<==Child()(in<==c.out);} \
         component main=Check();",
    )]);
    let graph = build_call_graph(&hir).unwrap();
    let DefinitionRef::Template(child) = hir.definition("Child").unwrap() else {
        panic!("Child template")
    };
    let check = hir.definition("Check").unwrap();
    let sites = graph.calls_from(CallOwner::Definition(check));
    assert_eq!(sites.len(), 2);
    assert!(sites.iter().all(|site| site.resolved() == Some(DefinitionRef::Template(child))));
    let mains = graph.calls_from(CallOwner::Main(0));
    assert_eq!(mains.len(), 1);
    assert_eq!(mains[0].resolved(), Some(check));
}

#[test]
fn unresolved_nested_anonymous_inputs_keep_owner_and_unattached_provenance() {
    let hir = fixture(&[(
        "nested.circom",
        "function Leaf(){return 1;} function Wrap(a){return a;} \
         template Child(){signal input in;signal output out;out<==in;} \
         template Check(){signal output y;y<==Child()(in<==Wrap(Leaf()));} \
         component main=Check();",
    )]);
    let graph = build_call_graph(&hir).unwrap();
    let check = hir.definition("Check").unwrap();
    let calls = graph.calls_from(CallOwner::Definition(check));
    assert_eq!(calls.len(), 3);
    assert!(calls.iter().all(|site| site.provenance == CallProvenance::Unattached));
    assert_eq!(graph.calls_from(CallOwner::Main(0)).len(), 1);
    assert!(graph.calls_from(CallOwner::Definition(hir.definition("Leaf").unwrap())).is_empty());
}

#[test]
fn missing_and_wrong_kind_targets_remain_unresolved() {
    let hir = fixture(&[(
        "incomplete.circom",
        "template T(){} function MissingUse(){return Absent();} \
         function WrongUse(){return T();}",
    )]);
    let graph = build_call_graph(&hir).unwrap();
    let missing = graph.calls_from(CallOwner::Definition(hir.definition("MissingUse").unwrap()));
    let wrong = graph.calls_from(CallOwner::Definition(hir.definition("WrongUse").unwrap()));
    assert_eq!(missing.len(), 1);
    assert_eq!(wrong.len(), 1);
    assert!(matches!(missing[0].target, CallTarget::Missing { .. }));
    assert!(matches!(wrong[0].target, CallTarget::WrongKind { .. }));
    assert_eq!(missing[0].resolved(), None);
    assert_eq!(wrong[0].resolved(), None);
}

#[test]
fn main_argument_call_is_not_owned_by_an_adjacent_definition() {
    let hir = fixture(&[(
        "main.circom",
        "function Seed(){return 1;} template Check(n){} component main=Check(Seed());",
    )]);
    let graph = build_call_graph(&hir).unwrap();
    let check = hir.definition("Check").unwrap();
    assert!(graph.calls_from(CallOwner::Definition(check)).is_empty());
    let main_calls = graph.calls_from(CallOwner::Main(0));
    assert_eq!(main_calls.len(), 2);
    assert!(main_calls.iter().any(|site| matches!(site.target, CallTarget::Function(_))));
    assert!(main_calls.iter().any(|site| site.expression.is_none()));
}

#[test]
fn opaque_assignment_call_is_owned_but_provisional() {
    let hir = fixture(&[(
        "opaque.circom",
        "function Id(a){return a;} template Check(){signal output y;y<==Id(1);}",
    )]);
    let graph = build_call_graph(&hir).unwrap();
    let check = hir.definition("Check").unwrap();
    let calls = graph.calls_from(CallOwner::Definition(check));
    assert_eq!(calls.len(), 1);
    assert_eq!(calls[0].provenance, CallProvenance::Provisional);
    assert!(calls[0].resolved().is_some());
}

#[test]
fn deferred_guard_makes_nested_component_call_provisional() {
    let hir = fixture(&[(
        "guard.circom",
        "template Child(){} template Check(n){if(n){component c=Child();}}",
    )]);
    let graph = build_call_graph(&hir).unwrap();
    let calls = graph.calls_from(CallOwner::Definition(hir.definition("Check").unwrap()));
    assert_eq!(calls.len(), 1);
    assert_eq!(calls[0].provenance, CallProvenance::DeferredControl);
    let field = FieldContext::for_curve(Curve::Bn254);
    let cfg = build_cfg(&hir, hir.definition("Check").unwrap()).unwrap();
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    assert!(matches!(
        graph.reachable_call(calls[0].id(), &facts),
        CallReachability::Unavailable(_)
    ));
}

#[test]
fn reachable_call_token_requires_a_checked_and_reachable_cfg_site() {
    let hir = fixture(&[(
        "reachability.circom",
        "template Child(){} template Check(){if(0){component dead=Child();} \
         component live=Child();}",
    )]);
    let definition = hir.definition("Check").unwrap();
    let graph = build_call_graph(&hir).unwrap();
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let calls = graph.calls_from(CallOwner::Definition(definition));
    assert_eq!(calls.len(), 2);
    assert!(matches!(graph.reachable_call(calls[0].id(), &facts), CallReachability::Unreachable));
    let CallReachability::Reachable(token) = graph.reachable_call(calls[1].id(), &facts) else {
        panic!("live component needs a certified call token")
    };
    assert_eq!(token.callee(), hir.definition("Child").unwrap());

    let other_graph = build_call_graph(&hir).unwrap();
    assert!(matches!(
        other_graph.reachable_call(calls[1].id(), &facts),
        CallReachability::Unavailable(_)
    ));

    let foreign = fixture(&[(
        "reachability.circom",
        "template Child(){} template Check(){if(0){component dead=Child();} \
         component live=Child();}",
    )]);
    let foreign_graph = build_call_graph(&foreign).unwrap();
    let foreign_call =
        foreign_graph.calls_from(CallOwner::Definition(foreign.definition("Check").unwrap()))[1];
    assert!(matches!(
        foreign_graph.reachable_call(foreign_call.id(), &facts),
        CallReachability::Unavailable(_)
    ));
}

#[test]
fn validated_main_has_a_reachable_root_token_without_a_definition_cfg() {
    let hir = fixture(&[("main.circom", "template Check(){} component main=Check();")]);
    let graph = build_call_graph(&hir).unwrap();
    let site = graph.calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(token) = graph.reachable_main_call(site.id(), &hir) else {
        panic!("validated main must be an analyzable root")
    };
    assert_eq!(token.callee(), hir.definition("Check").unwrap());
    let foreign = fixture(&[("foreign.circom", "template Check(){} component main=Check();")]);
    assert!(matches!(
        graph.reachable_main_call(site.id(), &foreign),
        CallReachability::Unavailable(_)
    ));
}

#[test]
fn independent_sequential_component_calls_keep_both_reachable() {
    let hir = fixture(&[(
        "instances.circom",
        "template Child(n){signal output out;out<==n;} \
         template Parent(){component c[2];c[0]=Child(0);c[1]=Child(1);}",
    )]);
    let definition = hir.definition("Parent").unwrap();
    let graph = build_call_graph(&hir).unwrap();
    let cfg = build_cfg(&hir, definition).unwrap();
    let field = FieldContext::for_curve(Curve::Bn254);
    let facts = analyze(&hir, &cfg, &field, None).unwrap();
    let calls = graph.calls_from(CallOwner::Definition(definition));
    assert_eq!(calls.len(), 2);
    for call in calls {
        assert!(matches!(graph.reachable_call(call.id(), &facts), CallReachability::Reachable(_)));
    }
}

#[test]
fn instantiation_preserves_parent_constraints_without_proving_child_outputs() {
    for (operator, expected) in [("<==", Incidence::Must), ("<--", Incidence::Zero)] {
        let source = format!(
            "template Child(){{signal input in;signal output out;out<==in;}} \
             template Parent(){{signal input x;signal output y;component c=Child(); \
             c.in{operator}x;y<==1;}}"
        );
        let hir = fixture(&[("parent.circom", &source)]);
        let definition = hir.definition("Parent").unwrap();
        let cfg = build_cfg(&hir, definition).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let facts = analyze(&hir, &cfg, &field, None).unwrap();
        let DefinitionRef::Template(parent) = definition else { panic!("parent template") };
        let input = hir.template(parent).unwrap().ports[0];
        let output = hir.template(parent).unwrap().ports[1];
        let x = facts.port_handle(input, &[]).unwrap();
        let y = facts.port_handle(output, &[]).unwrap();
        assert_eq!(facts.incidence_handle(&x).certified(), Some(&expected));
        assert_eq!(facts.incidence_handle(&y).certified(), Some(&Incidence::Must));

        let DefinitionRef::Template(child) = hir.definition("Child").unwrap() else {
            panic!("child template")
        };
        let child_output = hir.template(child).unwrap().ports[1];
        let handle =
            facts.component_output_handle(hir.components()[0].id, &[], child_output, &[]).unwrap();
        assert!(facts
            .incidence_handle(&handle)
            .unavailable()
            .is_some_and(|blockers| blockers.contains(&FactBlocker::ExternalSummary)));
    }
}
