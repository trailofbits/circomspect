// Tests intentionally fail by panicking; fixture assembly favors readable assertions.
// Rust 1.74 requires `allow` here because `expect` lint attributes are not yet stable.
#![allow(
    clippy::allow_attributes,
    clippy::expect_used,
    clippy::format_push_string,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::unwrap_used
)]
use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::{BitDecomposition, Fact, FactBlocker};
use circomspect_program_analysis::interprocedural::ProjectSummaries;
use num_bigint_dig::BigInt;
use parser::hir::{lift_project, AccessPath, AccessStep, ArrayIndex, HirProject, SymbolKind};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn source(boolean: [bool; 3], weight: usize, generated: bool) -> String {
    let mut body = String::from(
        "template Bits(){signal input in;signal output bits[3];\
         bits[0]<--0;bits[1]<--0;bits[2]<--0;",
    );
    for (index, enabled) in boolean.iter().enumerate() {
        if *enabled {
            body.push_str(&format!("bits[{index}]*(bits[{index}]-1)===0;"));
        }
    }
    let relation =
        format!("in{}bits[0]+2*bits[1]+{weight}*bits[2];", if generated { "===" } else { "<--" });
    body.push_str(&relation);
    body.push('}');
    body
}

fn unrolled_source(count: usize) -> String {
    let mut source = format!("template Bits(){{signal input in;signal output bits[{count}];");
    let mut terms = Vec::with_capacity(count);
    for index in 0..count {
        source.push_str(&format!("bits[{index}]<--0;"));
        source.push_str(&format!("bits[{index}]*(bits[{index}]-1)===0;"));
        let weight = BigInt::from(1u8) << index;
        terms.push(format!("{weight}*bits[{index}]"));
    }
    source.push_str("in===");
    source.push_str(&terms.join("+"));
    source.push_str(";}");
    source
}

fn accumulated_source(extra: &str) -> String {
    let mut source = source([true; 3], 4, true);
    source = source.replace(
        "in===bits[0]+2*bits[1]+4*bits[2];",
        &format!("var sum=0;sum+=bits[0];sum+=2*bits[1];sum+=4*bits[2];{extra}sum===in;"),
    );
    source
}

#[test]
fn exact_accumulated_variable_can_prove_reconstruction() {
    let fact = inspect(&accumulated_source(""), Curve::Bn254);
    let certificate = fact.certified().unwrap().as_ref().unwrap();
    assert_eq!(certificate.bits().len(), 3);
}

#[test]
fn overwritten_accumulator_cannot_keep_the_old_reconstruction() {
    let fact = inspect(&accumulated_source("sum=0;"), Curve::Bn254);
    assert!(fact.certified().and_then(Option::as_ref).is_none(), "{fact:?}");
}

#[test]
fn unsupported_compound_and_branch_joins_cannot_keep_symbolic_reconstruction() {
    let compound = inspect(&accumulated_source("sum*=1;"), Curve::Bn254);
    assert!(compound.unavailable().is_some(), "{compound:?}");

    let branch = accumulated_source("")
        .replace("template Bits()", "template Bits(n)")
        .replace("sum+=4*bits[2];", "if(n){sum+=4*bits[2];}");
    let fact = inspect(&branch, Curve::Bn254);
    assert!(fact.certified().and_then(Option::as_ref).is_none(), "{fact:?}");
}

#[test]
fn witness_value_from_accumulator_is_not_generated_reconstruction() {
    let source = accumulated_source("")
        .replace("signal input in;", "signal output in;")
        .replace("sum===in;", "in<--sum;");
    let fact = inspect(&source, Curve::Bn254);
    assert!(fact.certified().and_then(Option::as_ref).is_none(), "{fact:?}");
}

fn signal_path(hir: &HirProject, name: &str, index: Option<usize>) -> AccessPath {
    let symbol = hir
        .symbols()
        .iter()
        .find(|symbol| symbol.name == name && symbol.kind == SymbolKind::Signal)
        .unwrap();
    let steps = index.map_or_else(Vec::new, |index| {
        vec![AccessStep::Index {
            index: ArrayIndex::Constant(index.to_string()),
            span: symbol.span,
        }]
    });
    AccessPath {
        root: symbol.id,
        terminal: symbol.id,
        steps,
        component_input: false,
        component_output: false,
        span: symbol.span,
    }
}

fn inspect(source: &str, curve: Curve) -> Fact<Option<BitDecomposition>> {
    inspect_count(source, curve, 3)
}

fn inspect_count(source: &str, curve: Curve, count: usize) -> Fact<Option<BitDecomposition>> {
    let indices: Vec<_> = (0..count).collect();
    inspect_indices(source, curve, &indices)
}

fn inspect_indices(
    source: &str,
    curve: Curve,
    indices: &[usize],
) -> Fact<Option<BitDecomposition>> {
    inspect_indices_with_budget(source, curve, indices, None)
}

fn inspect_indices_with_budget(
    source: &str,
    curve: Curve,
    indices: &[usize],
    budget: Option<usize>,
) -> Fact<Option<BitDecomposition>> {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-bits-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    assert!(lifted.diagnostics.is_empty(), "{:?}", lifted.diagnostics);
    let definition = lifted.hir.definition("Bits").unwrap();
    let provider = ProjectSummaries::build(&lifted, curve).unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, budget).unwrap();
    let input = signal_path(&lifted.hir, "in", None);
    let bits: Vec<_> =
        indices.iter().map(|index| signal_path(&lifted.hir, "bits", Some(*index))).collect();
    facts.bit_decomposition(&input, &bits)
}

#[test]
fn explicit_unrolled_boolean_and_weighted_relations_certify_three_bits() {
    let source = source([true; 3], 4, true);
    let fact = inspect(&source, Curve::Bn254);
    let certificate = fact.certified().unwrap().as_ref().unwrap();
    assert_eq!(certificate.bits().len(), 3);
    assert_eq!(certificate.boolean_origins().len(), 3);
    assert_eq!(certificate.reconstruction_origins().len(), 1);
    let boolean = certificate.boolean_origins()[0][0].span;
    assert_eq!(&source[boolean.start()..boolean.end()], "bits[0]*(bits[0]-1)===0;");
    let reconstruction = certificate.reconstruction_origins()[0].span;
    assert_eq!(
        &source[reconstruction.start()..reconstruction.end()],
        "in===bits[0]+2*bits[1]+4*bits[2];"
    );
    assert_eq!(certificate.curve(), &Curve::Bn254);
}

#[test]
fn missing_boolean_wrong_weight_and_witness_only_relation_do_not_certify() {
    let witness_only = source([true; 3], 4, false).replace("signal input in;", "signal output in;");
    for source in [source([true, false, true], 4, true), source([true; 3], 3, true), witness_only] {
        let fact = inspect(&source, Curve::Bn254);
        assert!(fact.certified().unwrap().is_none(), "unexpected certificate: {fact:?}");
    }
}

#[test]
fn unsupported_extra_constraint_blocks_complete_local_relation_claim() {
    let mut source = source([true; 3], 4, true);
    source.pop();
    source.push_str("bits[0]*bits[1]*bits[2]===0;}");
    let fact = inspect(&source, Curve::Bn254);
    assert!(fact.unavailable().is_some(), "cubic constraint requires abstention: {fact:?}");
}

#[test]
fn symbolic_branch_cannot_supply_a_universal_boolean_equation() {
    let source = source([true; 3], 4, true)
        .replace("template Bits()", "template Bits(n)")
        .replace("bits[0]*(bits[0]-1)===0;", "if(n){bits[0]*(bits[0]-1)===0;}");
    let fact = inspect(&source, Curve::Bn254);
    assert!(fact.certified().and_then(Option::as_ref).is_none(), "{fact:?}");
}

#[test]
fn unrelated_unready_reads_and_input_reassignment_withhold_decomposition() {
    for extra in
        ["signal s;var y=s;s<--0;", "in<--0;", "signal input a[1];signal input i;var y=a[i];"]
    {
        let mut source = source([true; 3], 4, true);
        source.pop();
        source.push_str(extra);
        source.push('}');
        let fact = inspect(&source, Curve::Bn254);
        assert!(fact.unavailable().is_some(), "unsafe body must withhold proof: {fact:?}");
    }
}

#[test]
fn possible_unrelated_repeated_write_withholds_whole_body_relation() {
    let mut source = source([true; 3], 4, true).replace("template Bits()", "template Bits(n)");
    source.pop();
    source.push_str("signal s;s<--0;if(n){s<--1;}}");
    let fact = inspect(&source, Curve::Bn254);
    assert!(fact.unavailable().is_some(), "possible invalid branch must block: {fact:?}");
}

#[test]
fn unresolved_unrelated_witness_target_withholds_whole_body_relation() {
    let mut source = source([true; 3], 4, true);
    source.pop();
    source.push_str("signal input index;signal s[2];s[index]<--0;}");
    let fact = inspect(&source, Curve::Bn254);
    assert!(fact.unavailable().is_some(), "unresolved witness target must block: {fact:?}");
}

#[test]
fn dead_and_mutually_exclusive_writes_keep_local_relation_available() {
    for extra in ["signal s;s<--0;if(0){s<--1;}", "signal s;if(n){s<--0;}else{s<--1;}"] {
        let mut source = source([true; 3], 4, true).replace("template Bits()", "template Bits(n)");
        source.pop();
        source.push_str(extra);
        source.push('}');
        let fact = inspect(&source, Curve::Bn254);
        assert!(fact.certified().is_some_and(Option::is_some), "{fact:?}");
    }
}

#[test]
fn bit_paths_require_exact_distinct_ordered_in_bounds_elements() {
    let source = source([true; 3], 4, true);
    for indices in [[0, 1, 1], [1, 0, 2]] {
        let fact = inspect_indices(&source, Curve::Bn254, &indices);
        assert!(fact.certified().is_some_and(Option::is_none), "{fact:?}");
    }
    let out_of_bounds = inspect_indices(&source, Curve::Bn254, &[0, 1, 3]);
    assert!(out_of_bounds.unavailable().is_some(), "{out_of_bounds:?}");
}

#[test]
fn empty_and_over_budget_bit_lists_withhold_certificates() {
    let source = source([true; 3], 4, true);
    for count in [0, 513] {
        let fact = inspect_count(&source, Curve::Bn254, count);
        assert!(fact.unavailable().is_some(), "count {count}: {fact:?}");
    }
}

#[test]
fn incomplete_solver_cannot_release_provisional_bit_equations() {
    let source = source([true; 3], 4, true);
    let fact = inspect_indices_with_budget(&source, Curve::Bn254, &[0, 1, 2], Some(0));
    let blockers = fact.unavailable().unwrap();
    assert!(blockers.iter().any(|blocker| {
        let FactBlocker::Budget(_) = blocker else { return false };
        true
    }));
}

fn prove_unrolled(count: usize, curve: Curve) {
    let source = unrolled_source(count);
    let fact = inspect_count(&source, curve, count);
    assert!(fact.certified().and_then(Option::as_ref).is_some(), "{fact:?}");
    let certificate = fact.certified().unwrap().as_ref().unwrap();
    assert_eq!(certificate.bits().len(), count);
}

#[test]
fn unrolled_goldilocks_bits_prove_all_indexed_bits() {
    prove_unrolled(64, Curve::Goldilocks);
}

#[test]
fn unrolled_bn254_bits_prove_all_indexed_bits() {
    prove_unrolled(254, Curve::Bn254);
}

#[test]
fn equivalent_branch_equations_keep_every_source_origin() {
    let source = source([true; 3], 4, true).replace("template Bits()", "template Bits(n)").replace(
        "bits[0]*(bits[0]-1)===0;",
        "if(n){bits[0]*(bits[0]-1)===0;}else{0===2*bits[0]*(bits[0]-1);}",
    );
    let fact = inspect(&source, Curve::Bn254);
    let certificate = fact.certified().unwrap().as_ref().unwrap();
    assert_eq!(certificate.boolean_origins()[0].len(), 2);
}

#[test]
fn repeated_unrelated_signal_write_prevents_body_certificate() {
    for extra in ["signal s;s<--1;s<--2;", "signal s;s<--1;if(n){s<--2;}"] {
        let mut source = source([true; 3], 4, true).replace("template Bits()", "template Bits(n)");
        source.pop();
        source.push_str(extra);
        source.push('}');
        let fact = inspect(&source, Curve::Bn254);
        assert!(fact.unavailable().is_some(), "invalid write must block: {fact:?}");
    }
}

#[test]
fn body_relation_does_not_claim_two_representations_survive_other_equations() {
    let mut source = source([true; 3], 4, true);
    source.pop();
    source.push_str("bits[0]===0;bits[1]===0;bits[2]===0;}");
    let fact = inspect(&source, Curve::Bn254);
    assert!(fact.certified().and_then(Option::as_ref).is_some(), "{fact:?}");
}

#[test]
fn independent_decomposition_budgets_do_not_promote_missing_or_wrong_relations() {
    for budget in 0..65 {
        for source in [source([true, false, true], 4, true), source([true; 3], 3, true)] {
            let fact = inspect_indices_with_budget(&source, Curve::Bn254, &[0, 1, 2], Some(budget));
            assert!(
                fact.certified().and_then(Option::as_ref).is_none(),
                "budget={budget}: {fact:?}"
            );
        }
    }
}

#[test]
fn independent_dead_and_disjoint_unrelated_writes_preserve_relations() {
    for extra in [
        "signal s;s<--1;if(0){s<--2;}",
        "signal s;if(n){s<--1;}else{s<--2;}",
        "signal s[2];s[0]<--1;s[1]<--2;",
    ] {
        let mut source = source([true; 3], 4, true).replace("template Bits()", "template Bits(n)");
        source.pop();
        source.push_str(extra);
        source.push('}');
        let fact = inspect(&source, Curve::Bn254);
        assert!(fact.certified().and_then(Option::as_ref).is_some(), "{extra}: {fact:?}");
    }
}
