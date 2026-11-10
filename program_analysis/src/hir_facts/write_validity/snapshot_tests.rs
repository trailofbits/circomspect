use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{EdgeId, FlowGraph, NodeId};
use abstract_interpretation::solver::{
    solve, DataflowAnalysis, Forward, NodeFacts, SolveResult, Transfer, TransferOutcome,
};

use crate::hir_cfg::{CfgEdge, CfgNode, CfgNodeKind, DefinitionCfg, EdgeKind};
use crate::hir_facts::write_validity::tests::with_fixture;
use crate::hir_facts::write_validity::{WriteAnalysis, WriteState};
use crate::hir_facts::write_validity::{BodyWriteResult, BodyWriteSolve};
use crate::hir_facts::{AccessKey, AnalysisFacts, FactBlocker, forward_pruned_edges};
use crate::interprocedural::ProjectAnalysis;

type ActualState = <WriteAnalysis as DataflowAnalysis<DefinitionCfg>>::State;
type OwnedResult = SolveResult<NodeId, EdgeId, WriteState, String>;
type ActualResult = SolveResult<NodeId, EdgeId, ActualState, String>;

struct OwnedWriteAnalysis(WriteAnalysis);

impl DataflowAnalysis<DefinitionCfg> for OwnedWriteAnalysis {
    type State = WriteState;
    type Reason = String;

    fn boundary(&self, _: NodeId) -> WriteState {
        WriteState::empty()
    }
}

impl Transfer<OwnedWriteAnalysis, WriteState, String> for CfgNode {
    fn apply(
        &self,
        analysis: &OwnedWriteAnalysis,
        input: &WriteState,
    ) -> TransferOutcome<WriteState, String> {
        let mut state = input.clone();
        if let Some(key) = analysis.0.exact_writes.get(&self.id) {
            state.write(key);
        }
        TransferOutcome::Known(state)
    }
}

impl Transfer<OwnedWriteAnalysis, WriteState, String> for CfgEdge {
    fn apply(
        &self,
        analysis: &OwnedWriteAnalysis,
        input: &WriteState,
    ) -> TransferOutcome<WriteState, String> {
        if analysis.0.pruned.contains(&self.id) {
            TransferOutcome::Known(WriteState::Unreachable)
        } else {
            TransferOutcome::Known(input.clone())
        }
    }
}

fn write_analysis(cfg: &DefinitionCfg, pruned: BTreeSet<EdgeId>) -> WriteAnalysis {
    let mut exact_writes = BTreeMap::new();
    for id in cfg.nodes() {
        let Some(CfgNodeKind::Witness { target, .. }) = cfg.node(*id).map(|node| &node.kind) else {
            continue;
        };
        assert!(target.steps.is_empty());
        exact_writes.insert(*id, AccessKey { root: target.root, instance: None, steps: vec![] });
    }
    WriteAnalysis { exact_writes, pruned }
}

fn owned_snapshot(state: &WriteState) -> WriteState {
    state.clone()
}

fn owned_facts(
    facts: &BTreeMap<NodeId, NodeFacts<ActualState>>,
) -> BTreeMap<NodeId, NodeFacts<WriteState>> {
    let mut result = BTreeMap::new();
    for (id, facts) in facts {
        result.insert(
            *id,
            NodeFacts {
                input: facts.input.as_ref().map(|state| owned_snapshot(state)),
                output: facts.output.as_ref().map(|state| owned_snapshot(state)),
            },
        );
    }
    result
}

fn assert_same_solution(actual: ActualResult, expected: OwnedResult) {
    match (actual, expected) {
        (SolveResult::Complete(actual), SolveResult::Complete(expected)) => {
            assert_eq!(owned_facts(&actual), *expected);
        }
        (
            SolveResult::Incomplete { provisional_facts: actual, blockers: actual_blockers },
            SolveResult::Incomplete { provisional_facts: expected, blockers: expected_blockers },
        ) => {
            assert_eq!(owned_facts(&actual), *expected);
            assert_eq!(actual_blockers, expected_blockers);
        }
        (actual, expected) => panic!("different completion: {actual:?} != {expected:?}"),
    }
}

#[test]
fn shared_write_snapshots_preserve_every_fact_and_budget_boundary() {
    let source = "template T(n){signal output x;signal output y;
        if(n){x<--1;}else{y<--1;}while(n){x<--2;}x<--3;}";
    with_fixture(source, |_, cfg, _| {
        let loops = cfg
            .edges()
            .iter()
            .copied()
            .filter(|id| cfg.edge(*id).unwrap().payload.kind == EdgeKind::Loop)
            .collect();
        for pruned in [BTreeSet::new(), loops] {
            let actual = write_analysis(cfg, pruned.clone());
            let expected = OwnedWriteAnalysis(write_analysis(cfg, pruned));
            for budget in (0..128).map(Some).chain([None]) {
                let actual = solve::<_, _, Forward>(cfg, &actual, budget).unwrap();
                let expected = solve::<_, _, Forward>(cfg, &expected, budget).unwrap();
                assert_same_solution(actual, expected);
            }
        }
    });
}

fn known(outcome: TransferOutcome<ActualState, String>) -> ActualState {
    let TransferOutcome::Known(state) = outcome else { panic!("write transfer is exact") };
    state
}

fn written_key<'a>(state: &'a WriteState, key: &AccessKey) -> &'a AccessKey {
    let WriteState::Reached { may_written, .. } = state else { panic!("reachable write") };
    may_written.get(key).unwrap()
}

fn has_repeat(state: &WriteState, key: &AccessKey) -> bool {
    let WriteState::Reached { may_repeat, .. } = state else { panic!("reachable write") };
    may_repeat.contains(key)
}

#[test]
fn identity_transfers_reuse_storage_and_writes_preserve_prior_snapshots() {
    with_fixture("template T(){signal output x;x<--1;x<--2;}", |_, cfg, _| {
        let analysis = write_analysis(cfg, BTreeSet::new());
        let (&site, key) = analysis.exact_writes.first_key_value().unwrap();
        let written =
            known(cfg.node(site).unwrap().apply(&analysis, &analysis.boundary(cfg.entry())));
        let unchanged = known(cfg.node(cfg.exit()).unwrap().apply(&analysis, &written));
        assert!(std::ptr::eq(written_key(&written, key), written_key(&unchanged, key)));
        let edge = cfg.edge(cfg.edges()[0]).unwrap().payload;
        let unchanged = known(edge.apply(&analysis, &written));
        assert!(std::ptr::eq(written_key(&written, key), written_key(&unchanged, key)));
        let repeated = known(cfg.node(site).unwrap().apply(&analysis, &written));
        assert!(!has_repeat(&written, key));
        assert!(!has_repeat(&unchanged, key));
        assert!(has_repeat(&repeated, key));
    });
}

#[test]
fn unrolled_signal_arrays_keep_exact_write_and_read_results() {
    for duplicate in [false, true] {
        let tail = if duplicate { "x[255]<--7;" } else { "" };
        let source = format!(
            "template T(){{signal output x[256];
                for(var i=0;i<256;i++){{x[i]<--i;}}{tail}}}"
        );
        with_fixture(&source, |lifted, cfg, field| {
            let analysis = ProjectAnalysis::build(lifted, field.curve().clone()).unwrap();
            let evidence = analysis.contexts().symbolic_root(cfg.definition()).unwrap();
            let facts = analysis.contexts().analyze_for_evidence(cfg, &evidence, None).unwrap();
            assert_eq!(facts.definitely_repeats_any_body_write().certified(), Some(&duplicate));
            let no_repeats = facts.no_possible_repeated_body_writes();
            assert_eq!(no_repeats.certified().is_none(), duplicate, "{no_repeats:?}");
            assert_eq!(facts.body_signal_reads_ready().certified(), Some(&()));
        });
    }
}

fn reference_body_writes(facts: &AnalysisFacts<'_>) -> BodyWriteResult {
    let mut exact_writes = BTreeMap::new();
    let mut uncertain = Vec::new();
    for site in facts.cfg().nodes() {
        if facts.reachable_node(*site).certified() == Some(&false) {
            continue;
        }
        let node = facts.cfg().node(*site).unwrap();
        facts.classify_write(*site, &node.kind, &mut exact_writes, &mut uncertain);
    }
    facts.check_forward_write_budget(&uncertain)?;
    let analysis = WriteAnalysis {
        exact_writes,
        pruned: forward_pruned_edges(
            facts.hir,
            facts.cfg(),
            facts.field,
            &facts.forward,
            facts.calls.as_deref(),
        ),
    };
    match solve::<_, _, Forward>(facts.cfg(), &analysis, Some(100_000)).unwrap() {
        SolveResult::Complete(facts) => Ok(BodyWriteSolve { facts, uncertain }),
        SolveResult::Incomplete { blockers, .. } => {
            Err(blockers.iter().map(FactBlocker::from).collect())
        }
    }
}

#[test]
fn write_filter_preserves_incomplete_reached_and_dead_nodes() {
    let mut reached_blocked = 0;
    let mut dead = 0;
    let mut pending = 0;
    let sources = [
        "template T(){signal output x;if(0){x<--1;}x<--2;}",
        "template T(){signal input i;signal output x[2];x[0]<--1;x[i]<--2;}",
        "template T(n){signal output x;if(n){x<--1;}x<--2;}",
    ];
    for source in sources {
        with_fixture(source, |lifted, cfg, field| {
            for budget in [Some(0), Some(20), None] {
                let facts = crate::hir_facts::analyze(&lifted.hir, cfg, field, budget).unwrap();
                for site in facts.cfg().nodes() {
                    let reachable = facts.reachable_node(*site);
                    if reachable.certified() == Some(&false) {
                        dead += 1;
                    } else if reachable.unavailable().is_some() {
                        if facts.site_state(*site).is_some_and(|state| state.variables().is_some())
                        {
                            reached_blocked += 1;
                        } else {
                            pending += 1;
                        }
                    }
                }
                match (facts.compute_body_writes(), reference_body_writes(&facts)) {
                    (Ok(actual), Ok(expected)) => {
                        assert!(!actual.facts.is_empty());
                        assert_eq!(actual.facts, expected.facts);
                        assert_eq!(actual.uncertain.len(), expected.uncertain.len());
                        for (actual, expected) in actual.uncertain.iter().zip(&expected.uncertain) {
                            assert_eq!(actual.site, expected.site);
                            assert_eq!(actual.may_target, expected.may_target);
                            assert_eq!(actual.blockers, expected.blockers);
                        }
                    }
                    (Err(actual), Err(expected)) => {
                        assert!(!actual.is_empty());
                        assert_eq!(actual, expected);
                    }
                    (Ok(_), Err(_)) | (Err(_), Ok(_)) => panic!("completion changed"),
                }
            }
        });
    }
    assert!(reached_blocked > 0);
    assert!(dead > 0);
    assert!(pending > 0);
}
