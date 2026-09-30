use std::collections::BTreeSet;

use circomspect_abstract_interpretation::graph::{IndexedGraph, NodeId};
use circomspect_abstract_interpretation::lattice::{Constant, Lattice, Set};
use circomspect_abstract_interpretation::solver::{
    solve, Backward, DataflowAnalysis, Forward, SolveResult, Transfer, TransferOutcome,
};
use proptest::prelude::*;

#[derive(Clone)]
enum ConstantStep {
    Pass,
    Assign(i32),
}

struct Constants;

impl DataflowAnalysis<IndexedGraph<ConstantStep, ConstantStep>> for Constants {
    type State = Constant<i32>;
    type Reason = ();

    fn boundary(&self, _: NodeId) -> Self::State {
        Constant::bottom()
    }
}

impl Transfer<Constants, Constant<i32>, ()> for ConstantStep {
    fn apply(&self, _: &Constants, input: &Constant<i32>) -> TransferOutcome<Constant<i32>, ()> {
        match self {
            Self::Pass => TransferOutcome::Known(input.clone()),
            Self::Assign(value) => TransferOutcome::Known(Constant::Value(*value)),
        }
    }
}

#[test]
fn forward_constant_propagation_loses_conflicting_branch_values() {
    let graph = IndexedGraph::new(
        vec![
            ConstantStep::Pass,
            ConstantStep::Assign(7),
            ConstantStep::Assign(9),
            ConstantStep::Pass,
        ],
        vec![
            (NodeId::new(0), NodeId::new(1), ConstantStep::Pass),
            (NodeId::new(0), NodeId::new(2), ConstantStep::Pass),
            (NodeId::new(1), NodeId::new(3), ConstantStep::Pass),
            (NodeId::new(2), NodeId::new(3), ConstantStep::Pass),
        ],
        vec![NodeId::new(0)],
        vec![NodeId::new(3)],
    )
    .expect("valid graph");
    let result = solve::<_, _, Forward>(&graph, &Constants, None).expect("valid graph");
    let SolveResult::Complete(facts) = result else {
        panic!("finite constant domain must converge");
    };
    assert_eq!(facts[&NodeId::new(1)].output, Some(Constant::Value(7)));
    assert_eq!(facts[&NodeId::new(2)].output, Some(Constant::Value(9)));
    assert_eq!(facts[&NodeId::new(3)].input, Some(Constant::Top));
}

#[derive(Clone)]
struct LivenessStep {
    reads: Option<u8>,
    writes: Option<u8>,
}

struct Liveness;

impl DataflowAnalysis<IndexedGraph<LivenessStep, LivenessStep>> for Liveness {
    type State = Set<u8>;
    type Reason = ();

    fn boundary(&self, _: NodeId) -> Self::State {
        Set::bottom()
    }
}

impl Transfer<Liveness, Set<u8>, ()> for LivenessStep {
    fn apply(&self, _: &Liveness, input: &Set<u8>) -> TransferOutcome<Set<u8>, ()> {
        let mut result = Set::bottom();
        for &value in input.iter() {
            if Some(value) != self.writes {
                result.insert(value);
            }
        }
        if let Some(value) = self.reads {
            result.insert(value);
        }
        TransferOutcome::Known(result)
    }
}

#[test]
fn backward_liveness_joins_exits_then_applies_kill_and_gen() {
    let pass = LivenessStep { reads: None, writes: None };
    let graph = IndexedGraph::new(
        vec![
            LivenessStep { reads: Some(3), writes: Some(1) },
            LivenessStep { reads: Some(1), writes: None },
            LivenessStep { reads: Some(2), writes: None },
        ],
        vec![
            (NodeId::new(0), NodeId::new(1), pass.clone()),
            (NodeId::new(0), NodeId::new(2), pass),
        ],
        vec![NodeId::new(0)],
        vec![NodeId::new(1), NodeId::new(2)],
    )
    .expect("valid graph");
    let result = solve::<_, _, Backward>(&graph, &Liveness, None).expect("valid graph");
    let SolveResult::Complete(facts) = result else {
        panic!("finite liveness domain must converge");
    };
    let output: BTreeSet<_> = facts[&NodeId::new(0)]
        .output
        .as_ref()
        .expect("entry is reachable backwards")
        .iter()
        .copied()
        .collect();
    let input: BTreeSet<_> = facts[&NodeId::new(0)]
        .input
        .as_ref()
        .expect("entry is reachable backwards")
        .iter()
        .copied()
        .collect();
    assert_eq!(output, BTreeSet::from([1, 2]));
    assert_eq!(input, BTreeSet::from([2, 3]));
}

fn generated_constant(code: u8) -> Constant<i32> {
    match code % 4 {
        0 => Constant::Bottom,
        1 => Constant::Value(7),
        2 => Constant::Value(9),
        _ => Constant::Top,
    }
}

fn generated_live(bits: u8) -> Set<u8> {
    let mut result = Set::bottom();
    for value in 0..4 {
        if bits & (1 << value) != 0 {
            result.insert(value);
        }
    }
    result
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(96))]

    #[test]
    fn constant_transfer_is_monotone(a in any::<u8>(), b in any::<u8>()) {
        let left = generated_constant(a);
        let right = generated_constant(b);
        if left.leq(&right) {
            for step in [ConstantStep::Pass, ConstantStep::Assign(11)] {
                let TransferOutcome::Known(lower) = step.apply(&Constants, &left) else {
                    panic!("constant transfer is total");
                };
                let TransferOutcome::Known(upper) = step.apply(&Constants, &right) else {
                    panic!("constant transfer is total");
                };
                prop_assert!(lower.leq(&upper));
            }
        }
    }

    #[test]
    fn liveness_transfer_is_monotone(
        a in any::<u8>(), b in any::<u8>(), read in 0u8..5, write in 0u8..5,
    ) {
        let lower = generated_live(a & b);
        let upper = generated_live(a | b);
        let step = LivenessStep {
            reads: if read == 4 { None } else { Some(read) },
            writes: if write == 4 { None } else { Some(write) },
        };
        let TransferOutcome::Known(left) = step.apply(&Liveness, &lower) else {
            panic!("liveness transfer is total");
        };
        let TransferOutcome::Known(right) = step.apply(&Liveness, &upper) else {
            panic!("liveness transfer is total");
        };
        prop_assert!(lower.leq(&upper));
        prop_assert!(left.leq(&right));
    }
}
