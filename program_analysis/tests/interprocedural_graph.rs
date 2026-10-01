use circomspect_program_analysis::interprocedural::{build_call_graph, CallOwner, CallProvenance};
use parser::hir::{lower_project, CallTarget, DefinitionRef, HirProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
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
    let lowered = lower_project(&loaded);
    assert!(lowered.syntax_diagnostics.is_empty(), "{:?}", lowered.syntax_diagnostics);
    lowered.hir
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
    assert!(hir.mains.is_empty());
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
