use std::fs;

use circomspect_program_analysis::hir_cfg::build_cfg;
use circomspect_program_analysis::hir_facts::{
    BitAmbiguity, BitAmbiguityOutcome, FieldContext, NoBitAmbiguityCertificate,
};
use circomspect_program_analysis::interprocedural::{
    CallOwner, CallReachability, ProjectSummaries, SummaryFact,
};
use circomspect_program_analysis::new_rules::RuleContext;
use num_bigint_dig::BigInt;
use parser::hir::{lift_project, AccessPath, AccessStep, ArrayIndex, HirProject, LiftedProject};
use parser::new_frontend::{load_sources, Version, VersionPolicy};
use program_structure::utils::constants::Curve;

fn fixture(source: &str) -> LiftedProject {
    let directory = std::env::temp_dir().join(format!(
        "circomspect-bit-models-{}-{:?}",
        std::process::id(),
        std::thread::current().id()
    ));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("case.circom");
    fs::write(&path, source).unwrap();
    let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
    let lifted = lift_project(&loaded);
    assert!(lifted.syntax_diagnostics.is_empty(), "{:?}", lifted.syntax_diagnostics);
    lifted
}

fn path(hir: &HirProject, name: &str, index: Option<usize>) -> AccessPath {
    let symbol = hir.symbols().iter().find(|symbol| symbol.name == name).unwrap();
    let mut steps = Vec::new();
    if let Some(index) = index {
        steps.push(AccessStep::Index {
            index: ArrayIndex::Constant(index.to_string()),
            span: symbol.span,
        });
    }
    AccessPath {
        root: symbol.id,
        terminal: symbol.id,
        steps,
        component_input: false,
        component_output: false,
        span: symbol.span,
    }
}

fn source(width: usize, extra: &str) -> String {
    let mut source = format!("template T(){{signal input in;signal output bits[{width}];");
    let mut sum = String::new();
    let mut weight = BigInt::from(1);
    for index in 0..width {
        source.push_str(&format!("bits[{index}]<--0;bits[{index}]*(bits[{index}]-1)===0;"));
        if index != 0 {
            sum.push('+');
        }
        sum.push_str(&format!("{weight}*bits[{index}]"));
        weight *= 2;
    }
    source.push_str(&format!("in==={sum};{extra}}}"));
    source
}

fn inspect(
    source: &str,
    curve: Curve,
    width: usize,
    budget: Option<usize>,
) -> SummaryFact<BitAmbiguityOutcome> {
    let lifted = fixture(source);
    let provider = ProjectSummaries::build(&lifted, curve).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = if lifted.hir.mains().is_empty() {
        provider.symbolic_root(definition).unwrap()
    } else {
        let site = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph().reachable_main_call(site.id(), &lifted.hir)
        else {
            panic!("main must be reachable");
        };
        provider.main_evidence(&call).unwrap()
    };
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, budget).unwrap();
    let input = path(&lifted.hir, "in", None);
    let bits: Vec<_> = (0..width).map(|index| path(&lifted.hir, "bits", Some(index))).collect();
    let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
    context.template_bit_ambiguity(&input, &bits)
}

fn certificate(result: &SummaryFact<BitAmbiguityOutcome>) -> &BitAmbiguity {
    let Some(BitAmbiguityOutcome::Proved(certificate)) = result.certified() else {
        panic!("expected a verified pair: {result:?}");
    };
    certificate
}

fn verify_pair(certificate: &BitAmbiguity, width: usize, expected_input: i64) {
    let field = FieldContext::for_curve(certificate.decomposition().curve().clone());
    let expected_input = field.canonical(expected_input.into());
    assert_eq!(certificate.input_value(), &expected_input);
    let representations = certificate.representations();
    assert_ne!(representations[0].bits(), representations[1].bits());
    for (representation, assignment) in representations.iter().zip(certificate.assignments()) {
        assert_eq!(representation.bits().len(), width);
        let mut integer = BigInt::from(0);
        let mut weight = BigInt::from(1);
        for (bit, key) in representation.bits().iter().zip(certificate.decomposition().bits()) {
            let value = field.canonical(i32::from(*bit).into());
            assert_eq!(assignment.get(key), Some(&value));
            let boolean =
                field.multiply(&value, &field.subtract(&value, &field.canonical(1.into())));
            assert!(field.is_zero(&boolean));
            if *bit {
                integer += &weight;
            }
            weight *= 2;
        }
        assert_eq!(&integer.to_biguint().unwrap(), representation.integer());
        assert_eq!(field.canonical(integer), expected_input);
        assert_eq!(assignment.get(certificate.decomposition().input()), Some(&expected_input));
    }
    let difference = representations[1].integer() - representations[0].integer();
    assert_eq!(field.canonical(BigInt::from(difference)), field.canonical(0.into()));
}

#[test]
fn field_boundaries_prove_two_complete_models_only_when_the_width_allows_them() {
    for (curve, width) in [(Curve::Bn254, 254), (Curve::Goldilocks, 64), (Curve::Bls12_381, 255)] {
        let result = inspect(&source(width, ""), curve.clone(), width, None);
        let certificate = certificate(&result);
        verify_pair(certificate, width, 0);
        assert_eq!(certificate.constraint_origins().len(), width + 1);
        let below = inspect(&source(width - 1, ""), curve, width - 1, None);
        assert_eq!(
            below.certified(),
            Some(&BitAmbiguityOutcome::NoCertificate(
                NoBitAmbiguityCertificate::WidthBelowFieldModulus
            ))
        );
    }
}

#[test]
fn generated_input_seeds_and_extra_fixed_signals_are_checked_in_both_models() {
    let source = source(64, "in===1;signal s;s<--0;s===7;");
    let result = inspect(&source, Curve::Goldilocks, 64, None);
    let certificate = certificate(&result);
    verify_pair(certificate, 64, 1);
    assert_eq!(certificate.constraint_origins().len(), 67);
    let bits = certificate.decomposition().bits();
    for assignment in certificate.assignments() {
        let extra: Vec<_> = assignment
            .iter()
            .filter(|(key, _)| *key != certificate.decomposition().input() && !bits.contains(key))
            .map(|(_, value)| value.as_bigint().clone())
            .collect();
        assert_eq!(extra, [BigInt::from(7)]);
    }
}

#[test]
fn singleton_input_at_the_last_fitting_integer_is_accepted_but_next_is_not() {
    let accepted = inspect(&source(64, "in===4294967294;"), Curve::Goldilocks, 64, None);
    verify_pair(certificate(&accepted), 64, 4_294_967_294);
    let rejected = inspect(&source(64, "in===4294967295;"), Curve::Goldilocks, 64, None);
    assert_eq!(
        rejected.certified(),
        Some(&BitAmbiguityOutcome::NoCertificate(NoBitAmbiguityCertificate::CandidatesRejected))
    );
}

#[test]
fn additional_constraints_cannot_be_dropped_after_matching_the_decomposition() {
    for extra in ["bits[0]===0;", "0===1;", "in===0;in===1;", "signal s;s<--0;s*in===1;"] {
        let result = inspect(&source(64, extra), Curve::Goldilocks, 64, None);
        assert_eq!(
            result.certified(),
            Some(&BitAmbiguityOutcome::NoCertificate(
                NoBitAmbiguityCertificate::CandidatesRejected
            )),
            "{extra}: {result:?}"
        );
    }
}

#[test]
fn exact_auxiliary_zero_is_only_a_candidate_until_its_equation_is_validated() {
    let result = inspect(&source(64, "signal s;s<--1;s*in===0;"), Curve::Goldilocks, 64, None);
    verify_pair(certificate(&result), 64, 0);
}

#[test]
fn witness_constants_never_seed_a_constraint_fixed_input() {
    let source = source(64, "").replace("signal input in;", "signal in;in<--1;");
    let result = inspect(&source, Curve::Goldilocks, 64, None);
    verify_pair(certificate(&result), 64, 0);
}

#[test]
fn source_failures_unknown_assertions_and_components_withhold_models() {
    for extra in [
        "assert(0);",
        "var bad=1/0;",
        "signal bad[-1];",
        "assert(in==0);",
        "var bad=Missing();",
        "component c=Missing();",
        "signal a;signal b;b<--a;a<--0;",
        "signal s;s<--0;s<--1;",
        "in<--0;",
    ] {
        let result = inspect(&source(64, extra), Curve::Goldilocks, 64, None);
        assert!(result.unavailable().is_some(), "{extra}: {result:?}");
    }
}

#[test]
fn exact_dead_branches_and_constant_true_assertions_preserve_models() {
    let result = inspect(&source(64, "assert(1);if(0){bits[0]===0;}"), Curve::Goldilocks, 64, None);
    verify_pair(certificate(&result), 64, 0);
}

#[test]
fn unknown_template_control_cannot_borrow_a_pair_from_the_exit_intersection() {
    let source = source(64, "if(n){bits[0]===0;}").replace("template T()", "template T(n)");
    let symbolic = inspect(&source, Curve::Goldilocks, 64, None);
    assert!(symbolic.unavailable().is_some(), "{symbolic:?}");
    let exact = inspect(&format!("{source}component main=T(1);"), Curve::Goldilocks, 64, None);
    assert_eq!(
        exact.certified(),
        Some(&BitAmbiguityOutcome::NoCertificate(NoBitAmbiguityCertificate::CandidatesRejected))
    );
}

#[test]
fn incomplete_solver_cannot_release_exact_looking_partial_models() {
    let source = source(64, "");
    for budget in [0, 1, 64, 128] {
        let result = inspect(&source, Curve::Goldilocks, 64, Some(budget));
        assert!(result.unavailable().is_some(), "{budget}: {result:?}");
    }
    verify_pair(certificate(&inspect(&source, Curve::Goldilocks, 64, None)), 64, 0);
}

#[test]
fn queried_external_input_bits_cannot_change_between_models() {
    let mut source = source(64, "").replace("signal output bits", "signal input bits");
    for index in 0..64 {
        source = source.replace(&format!("bits[{index}]<--0;"), "");
    }
    let result = inspect(&source, Curve::Goldilocks, 64, None);
    assert!(result.unavailable().is_some(), "{result:?}");
}

#[test]
fn absent_boolean_relation_and_changed_weight_cannot_prove_ambiguity() {
    let missing = source(64, "").replace("bits[0]*(bits[0]-1)===0;", "");
    let wrong_weight = source(64, "").replace("2*bits[1]", "3*bits[1]");
    for source in [missing, wrong_weight] {
        let result = inspect(&source, Curve::Goldilocks, 64, None);
        assert_eq!(
            result.certified(),
            Some(&BitAmbiguityOutcome::NoCertificate(
                NoBitAmbiguityCertificate::NoMatchingDecomposition
            ))
        );
    }
}

#[test]
fn binding_cannot_be_reused_for_another_field_project_or_definition() {
    let source = format!("{}template Other(){{}}", source(64, ""));
    let lifted = fixture(&source);
    let provider = ProjectSummaries::build(&lifted, Curve::Goldilocks).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let input = path(&lifted.hir, "in", None);
    let bits: Vec<_> = (0..64).map(|index| path(&lifted.hir, "bits", Some(index))).collect();
    let other_curve = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
    let result = other_curve.template_bit_ambiguity(&facts, &evidence, &input, &bits);
    assert!(result.unavailable().is_some(), "{result:?}");
    let other_evidence = provider.symbolic_root(lifted.hir.definition("Other").unwrap()).unwrap();
    let result = provider.template_bit_ambiguity(&facts, &other_evidence, &input, &bits);
    assert!(result.unavailable().is_some(), "{result:?}");
    let foreign = fixture(&source);
    let foreign_provider = ProjectSummaries::build(&foreign, Curve::Goldilocks).unwrap();
    let result = foreign_provider.template_bit_ambiguity(&facts, &evidence, &input, &bits);
    assert!(result.unavailable().is_some(), "{result:?}");
    let foreign_input = path(&foreign.hir, "in", None);
    let result = provider.template_bit_ambiguity(&facts, &evidence, &foreign_input, &bits);
    assert!(result.unavailable().is_some(), "{result:?}");
    verify_pair(
        certificate(&provider.template_bit_ambiguity(&facts, &evidence, &input, &bits)),
        64,
        0,
    );
}

#[test]
fn a_called_leaf_does_not_claim_its_callers_constraint_domain_is_closed() {
    let source = format!(
        "{}template Parent(){{component c=T();c.in<==0;}}component main=Parent();",
        source(64, "")
    );
    let lifted = fixture(&source);
    let provider = ProjectSummaries::build(&lifted, Curve::Goldilocks).unwrap();
    let main_site = provider.graph().calls_from(CallOwner::Main(0))[0];
    let CallReachability::Reachable(main_call) =
        provider.graph().reachable_main_call(main_site.id(), &lifted.hir)
    else {
        panic!("main must be reachable");
    };
    let main = provider.main_evidence(&main_call).unwrap();
    let main_cfg = build_cfg(&lifted.hir, main.context().definition()).unwrap();
    let main_facts = provider.analyze_for_evidence(&main_cfg, &main, None).unwrap();
    let child_site =
        provider.graph().calls_from(CallOwner::Definition(main.context().definition()))[0];
    let CallReachability::Reachable(child_call) =
        provider.graph().reachable_call(child_site.id(), &main_facts)
    else {
        panic!("child must be reachable");
    };
    let child = provider.call_evidence(&child_call, &main_facts, &main).unwrap();
    let child_cfg = build_cfg(&lifted.hir, child.context().definition()).unwrap();
    let child_facts = provider.analyze_for_evidence(&child_cfg, &child, None).unwrap();
    let input = path(&lifted.hir, "in", None);
    let bits: Vec<_> = (0..64).map(|index| path(&lifted.hir, "bits", Some(index))).collect();
    let result = provider.template_bit_ambiguity(&child_facts, &child, &input, &bits);
    assert!(result.unavailable().is_some(), "{result:?}");
}

#[test]
fn a_rejected_default_candidate_does_not_prove_the_relation_is_unique() {
    let source = source(64, "signal s;s<--0;s*in===1;");
    let result = inspect(&source, Curve::Goldilocks, 64, None);
    assert_eq!(
        result.certified(),
        Some(&BitAmbiguityOutcome::NoCertificate(NoBitAmbiguityCertificate::CandidatesRejected))
    );
    let with_fixed_input = source.replacen("s*in===1;", "s*in===1;s===1;in===1;", 1);
    let result = inspect(&with_fixed_input, Curve::Goldilocks, 64, None);
    verify_pair(certificate(&result), 64, 1);
}

#[test]
fn exact_bounds_and_order_are_part_of_the_requested_relation() {
    let lifted = fixture(&source(64, ""));
    let provider = ProjectSummaries::build(&lifted, Curve::Goldilocks).unwrap();
    let definition = lifted.hir.definition("T").unwrap();
    let evidence = provider.symbolic_root(definition).unwrap();
    let cfg = build_cfg(&lifted.hir, definition).unwrap();
    let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
    let input = path(&lifted.hir, "in", None);
    let bits: Vec<_> = (0..64).map(|index| path(&lifted.hir, "bits", Some(index))).collect();
    let mut reordered = bits.clone();
    reordered.swap(0, 1);
    let mut duplicate = bits.clone();
    duplicate[1] = duplicate[0].clone();
    for paths in [reordered, duplicate] {
        let result = provider.template_bit_ambiguity(&facts, &evidence, &input, &paths);
        assert_eq!(
            result.certified(),
            Some(&BitAmbiguityOutcome::NoCertificate(
                NoBitAmbiguityCertificate::NoMatchingDecomposition
            ))
        );
    }
    let mut outside = bits.clone();
    outside[0] = path(&lifted.hir, "bits", Some(64));
    for paths in [outside, vec![], vec![bits[0].clone(); 513]] {
        let result = provider.template_bit_ambiguity(&facts, &evidence, &input, &paths);
        assert!(result.unavailable().is_some(), "{result:?}");
    }
}

#[test]
fn unrelated_missing_definitions_do_not_poison_a_complete_library_root() {
    let source = format!("{}template Broken(){{var x=Missing();}}", source(64, ""));
    let result = inspect(&source, Curve::Goldilocks, 64, None);
    verify_pair(certificate(&result), 64, 0);
}
#[test]
fn every_external_input_has_the_same_value_in_both_models() {
    let source = source(64, "signal input other;other===7;");
    let result = inspect(&source, Curve::Goldilocks, 64, None);
    let certificate = certificate(&result);
    verify_pair(certificate, 64, 0);
    let input = certificate.decomposition().input();
    let bits = certificate.decomposition().bits();
    let external: Vec<_> = certificate.assignments()[0]
        .keys()
        .filter(|key| *key != input && !bits.contains(key))
        .collect();
    assert_eq!(external.len(), 1);
    for assignment in certificate.assignments() {
        assert_eq!(assignment[external[0]].as_bigint(), &BigInt::from(7));
    }
    assert_eq!(certificate.constraint_origins().len(), 66);
}

#[test]
fn a_shared_external_input_cannot_follow_the_different_bit_vectors() {
    for extra in [
        "signal input other;bits[0]===other;",
        "signal input other;other===1;other*(bits[0]-1)===0;",
    ] {
        let result = inspect(&source(64, extra), Curve::Goldilocks, 64, None);
        assert_eq!(
            result.certified(),
            Some(&BitAmbiguityOutcome::NoCertificate(
                NoBitAmbiguityCertificate::CandidatesRejected
            )),
            "{extra}: {result:?}"
        );
    }
    let unconstrained = source(64, "signal input other;other*(bits[0]-1)===0;");
    let result = inspect(&unconstrained, Curve::Goldilocks, 64, None);
    let certificate = certificate(&result);
    verify_pair(certificate, 64, 0);
    let field = FieldContext::for_curve(Curve::Goldilocks);
    let input = certificate.decomposition().input();
    let bits = certificate.decomposition().bits();
    for assignment in certificate.assignments() {
        let external: Vec<_> =
            assignment.iter().filter(|(key, _)| *key != input && !bits.contains(key)).collect();
        assert_eq!(external.len(), 1);
        assert!(field.is_zero(external[0].1));
        let bit = &assignment[&bits[0]];
        let equation =
            field.multiply(external[0].1, &field.subtract(bit, &field.canonical(1.into())));
        assert!(field.is_zero(&equation));
    }
}
