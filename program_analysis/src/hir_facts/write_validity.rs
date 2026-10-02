//! Body witness-write multiplicity over the checked, specialized CFG.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{EdgeId, FlowGraph, NodeId};
use abstract_interpretation::lattice::Lattice;
use abstract_interpretation::solver::{
    solve, CertifiedFacts, DataflowAnalysis, Forward, SolveResult, Transfer, TransferOutcome,
};
use parser::hir::{AccessPath, AccessStep, ArrayIndex, ExprId, ProjectIdentity, SymbolKind};
use parser::new_frontend::{AssignmentOperator, PortDirection};

use crate::hir_cfg::{CfgEdge, CfgNode, CfgNodeKind, DefinitionCfg, Origin};
use crate::hir_facts::access::key_for_path;
use crate::hir_facts::{
    forward_pruned_edges, AccessHandle, AccessKey, AnalysisFacts, Fact, FactBlocker,
    SignalReadIssue, VisitAccesses, WitnessWriteIssue,
};
use crate::interprocedural::{ContextEvidence, ValidatedConstructorReads};

/// Proof that one exact target has no repeated body witness write in this scope.
/// Incoming component input initialization is outside this certificate's claim.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NoRepeatedBodyWrite {
    project: ProjectIdentity,
    evidence: Option<ContextEvidence>,
    target: AccessKey,
}

/// Result of checking one exact target's body witness-write multiplicity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BodyWriteStatus {
    NoRepeat(NoRepeatedBodyWrite),
    DefinitelyRepeated(RepeatedBodyWrite),
}

/// Candidate second-write sites for a target repeated on every exit path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RepeatedBodyWrite {
    project: ProjectIdentity,
    evidence: Option<ContextEvidence>,
    target: AccessKey,
    sites: Vec<Origin>,
}

impl RepeatedBodyWrite {
    #[must_use]
    pub fn sites(&self) -> &[Origin] {
        &self.sites
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum WriteState {
    Unreachable,
    Reached {
        may_written: BTreeSet<AccessKey>,
        must_written: BTreeSet<AccessKey>,
        may_repeat: BTreeSet<AccessKey>,
        must_repeat: BTreeSet<AccessKey>,
        must_repeat_any: bool,
    },
}

impl WriteState {
    fn empty() -> Self {
        Self::Reached {
            may_written: BTreeSet::new(),
            must_written: BTreeSet::new(),
            may_repeat: BTreeSet::new(),
            must_repeat: BTreeSet::new(),
            must_repeat_any: false,
        }
    }

    fn write(&mut self, key: &AccessKey) {
        let Self::Reached { may_written, must_written, may_repeat, must_repeat, must_repeat_any } =
            self
        else {
            return;
        };
        if may_written.contains(key) {
            may_repeat.insert(key.clone());
        }
        if must_written.contains(key) {
            must_repeat.insert(key.clone());
            *must_repeat_any = true;
        }
        may_written.insert(key.clone());
        must_written.insert(key.clone());
    }
}

impl Lattice for WriteState {
    fn bottom() -> Self {
        Self::Unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unreachable, _) => true,
            (Self::Reached { .. }, Self::Unreachable) => false,
            (
                Self::Reached {
                    may_written: left_may,
                    must_written: left_must,
                    may_repeat: left_possible,
                    must_repeat: left_certain,
                    must_repeat_any: left_any,
                },
                Self::Reached {
                    may_written: right_may,
                    must_written: right_must,
                    may_repeat: right_possible,
                    must_repeat: right_certain,
                    must_repeat_any: right_any,
                },
            ) => {
                left_may.is_subset(right_may)
                    && right_must.is_subset(left_must)
                    && left_possible.is_subset(right_possible)
                    && right_certain.is_subset(left_certain)
                    && (!right_any || *left_any)
            }
        }
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        if let Self::Unreachable = other {
            return false;
        }
        if let Self::Unreachable = self {
            *self = other.clone();
            return true;
        }
        let old = self.clone();
        let (
            Self::Reached {
                may_written: left_may,
                must_written: left_must,
                may_repeat: left_possible,
                must_repeat: left_certain,
                must_repeat_any: left_any,
            },
            Self::Reached {
                may_written: right_may,
                must_written: right_must,
                may_repeat: right_possible,
                must_repeat: right_certain,
                must_repeat_any: right_any,
            },
        ) = (&mut *self, other)
        else {
            return false;
        };
        left_may.extend(right_may.iter().cloned());
        left_must.retain(|key| right_must.contains(key));
        left_possible.extend(right_possible.iter().cloned());
        left_certain.retain(|key| right_certain.contains(key));
        *left_any &= right_any;
        *self != old
    }
}

struct WriteAnalysis {
    exact_writes: BTreeMap<NodeId, AccessKey>,
    pruned: BTreeSet<EdgeId>,
}

impl DataflowAnalysis<DefinitionCfg> for WriteAnalysis {
    type State = WriteState;
    type Reason = String;

    fn boundary(&self, _: NodeId) -> Self::State {
        WriteState::empty()
    }
}

impl Transfer<WriteAnalysis, WriteState, String> for CfgNode {
    fn apply(
        &self,
        analysis: &WriteAnalysis,
        input: &WriteState,
    ) -> TransferOutcome<WriteState, String> {
        let mut state = input.clone();
        if let Some(key) = analysis.exact_writes.get(&self.id) {
            state.write(key);
        }
        TransferOutcome::Known(state)
    }
}

impl Transfer<WriteAnalysis, WriteState, String> for CfgEdge {
    fn apply(
        &self,
        analysis: &WriteAnalysis,
        input: &WriteState,
    ) -> TransferOutcome<WriteState, String> {
        if analysis.pruned.contains(&self.id) {
            TransferOutcome::Known(WriteState::Unreachable)
        } else {
            TransferOutcome::Known(input.clone())
        }
    }
}

struct UncertainWrite {
    site: NodeId,
    may_target: Option<AccessKey>,
    blockers: BTreeSet<FactBlocker>,
}

impl UncertainWrite {
    fn may_alias(&self, target: &AccessKey) -> bool {
        match &self.may_target {
            Some(key) => key.may_alias(target),
            None => true,
        }
    }
}

type WriteFacts = CertifiedFacts<NodeId, WriteState>;

struct ReadCheck<'a> {
    site: NodeId,
    may: &'a BTreeSet<AccessKey>,
    must: &'a BTreeSet<AccessKey>,
    uncertain: &'a [UncertainWrite],
    blockers: &'a mut BTreeSet<FactBlocker>,
    constructor: &'a dyn Fn(ExprId) -> bool,
}

impl AnalysisFacts<'_> {
    /// Require every reachable signal read to have a prior exact body write
    /// or an input-port initialization; input-port writes are invalid.
    pub(crate) fn body_signal_reads_ready(&self) -> Fact<()> {
        self.body_signal_reads_ready_by(&|_| false)
    }

    /// Permit only provider-validated constructors bound to these exact source facts.
    pub(crate) fn body_signal_reads_ready_with(
        &self,
        constructors: &ValidatedConstructorReads,
    ) -> Fact<()> {
        if self.evidence_binding.as_ref() != Some(constructors.evidence()) {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        self.body_signal_reads_ready_by(&|call| constructors.contains(call))
    }

    fn body_signal_reads_ready_by(&self, constructor: &dyn Fn(ExprId) -> bool) -> Fact<()> {
        let (facts, uncertain) = match self.solve_body_writes() {
            Ok(result) => result,
            Err(blockers) => return Fact::blocked(blockers),
        };
        let mut blockers = BTreeSet::new();
        for site in self.cfg.nodes() {
            let Some(WriteState::Reached { may_written, must_written, .. }) =
                facts.get(site).and_then(|item| item.input.as_ref())
            else {
                continue;
            };
            let Some(node) = self.cfg.node(*site) else { continue };
            let mut check = ReadCheck {
                site: *site,
                may: may_written,
                must: must_written,
                uncertain: &uncertain,
                blockers: &mut blockers,
                constructor,
            };
            self.node_read_blockers(&node.kind, &mut check);
        }
        if blockers.is_empty() {
            Fact::known(())
        } else {
            Fact::blocked(blockers)
        }
    }

    fn node_read_blockers(&self, kind: &CfgNodeKind, check: &mut ReadCheck<'_>) {
        if let CfgNodeKind::Evaluate(expression) = kind {
            self.expression_read_blockers(*expression, check);
        }
        if let CfgNodeKind::Witness { target, value } = kind {
            if self.is_input_port(target) {
                check.blockers.insert(FactBlocker::WitnessWrite(
                    check.site,
                    WitnessWriteIssue::InputReassignment,
                ));
            }
            self.target_index_read_blockers(target, check);
            self.expression_read_blockers(*value, check);
        }
        if let CfgNodeKind::Constraint { target, left, right } = kind {
            if let Some(target) = target {
                self.target_index_read_blockers(target, check);
            }
            self.expression_read_blockers(*left, check);
            if let Some(right) = right {
                self.expression_read_blockers(*right, check);
            }
        }
    }

    fn target_index_read_blockers(&self, target: &AccessPath, check: &mut ReadCheck<'_>) {
        for step in &target.steps {
            if let AccessStep::Index { index: ArrayIndex::Symbolic(expression), .. } = step {
                self.expression_read_blockers(*expression, check);
            }
        }
    }

    fn expression_read_blockers(&self, expression: ExprId, check: &mut ReadCheck<'_>) {
        let constructor = check.constructor;
        let complete = expression.visit_accesses_with(
            self.hir,
            &|call| self.exact_call_value(call).is_some() || constructor(call),
            &mut |path| self.path_read_blockers(path, check),
        );
        if !complete {
            check.blockers.insert(FactBlocker::OpaqueExpression(expression));
        }
    }

    fn path_read_blockers(&self, path: &AccessPath, check: &mut ReadCheck<'_>) {
        let Some(symbol) = self.hir.symbol(path.terminal) else {
            check
                .blockers
                .insert(FactBlocker::SignalRead(check.site, SignalReadIssue::UnresolvedAccess));
            return;
        };
        match symbol.kind {
            SymbolKind::Signal => self.signal_read_blockers(path, check),
            SymbolKind::Parameter | SymbolKind::Variable => {}
            SymbolKind::Component | SymbolKind::Bus | SymbolKind::Tag => {
                check
                    .blockers
                    .insert(FactBlocker::SignalRead(check.site, SignalReadIssue::UnresolvedAccess));
            }
        }
    }

    fn signal_read_blockers(&self, path: &AccessPath, check: &mut ReadCheck<'_>) {
        if path.root != path.terminal {
            check
                .blockers
                .insert(FactBlocker::SignalRead(check.site, SignalReadIssue::UnresolvedAccess));
            return;
        }
        let key = self.exact_access_key(path);
        let Some(key) = key.certified() else {
            check.blockers.extend(key.unavailable().cloned().unwrap_or_default());
            return;
        };
        if self.is_input_port(path) {
            return;
        }
        if check.must.contains(key) {
            return;
        }
        let issue = if check.uncertain.iter().any(|write| write.may_alias(key)) {
            SignalReadIssue::UnresolvedPriorWrite
        } else if check.may.contains(key) {
            SignalReadIssue::BranchOnlyWrite
        } else {
            SignalReadIssue::NoPriorWrite
        };
        check.blockers.insert(FactBlocker::SignalRead(check.site, issue));
    }

    fn is_input_port(&self, path: &AccessPath) -> bool {
        self.hir
            .ports()
            .iter()
            .any(|port| port.symbol == path.root && port.direction == Some(PortDirection::Input))
    }

    /// Classify repeated body witness writes to one exact checked source target.
    pub fn body_write_status(&self, path: &AccessPath) -> Fact<BodyWriteStatus> {
        let key = self.exact_access_key(path);
        let Some(key) = key.certified() else {
            return Fact::blocked(key.unavailable().cloned().unwrap_or_default());
        };
        self.body_write_status_key(key)
    }

    pub(crate) fn body_write_status_handle(&self, handle: &AccessHandle) -> Fact<BodyWriteStatus> {
        let key = self.exact_handle_key(handle);
        let Some(key) = key.certified() else {
            return Fact::blocked(key.unavailable().cloned().unwrap_or_default());
        };
        self.body_write_status_key(key)
    }

    fn body_write_status_key(&self, key: &AccessKey) -> Fact<BodyWriteStatus> {
        let (facts, uncertain) = match self.solve_body_writes() {
            Ok(result) => result,
            Err(blockers) => return Fact::blocked(blockers),
        };
        let Some(WriteState::Reached { may_repeat, must_repeat, .. }) =
            facts.get(&self.cfg.exit()).and_then(|item| item.output.as_ref())
        else {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        };
        if must_repeat.contains(key) {
            return self.repeated_write_status(key, &facts);
        }
        let blockers = self.possible_write_blockers(key, &facts, may_repeat, &uncertain);
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        Fact::known(BodyWriteStatus::NoRepeat(NoRepeatedBodyWrite {
            project: self.hir.identity(),
            evidence: self.evidence_binding.clone(),
            target: key.clone(),
        }))
    }

    fn repeated_write_status(&self, key: &AccessKey, facts: &WriteFacts) -> Fact<BodyWriteStatus> {
        let sites = self.repeat_sites(facts, key);
        if sites.is_empty() {
            return Fact::blocked(BTreeSet::from([FactBlocker::WitnessWrite(
                self.cfg.exit(),
                WitnessWriteIssue::DefiniteRepeat,
            )]));
        }
        let sites = sites
            .into_iter()
            .filter_map(|site| self.cfg.node(site).and_then(|node| node.origin))
            .collect();
        Fact::known(BodyWriteStatus::DefinitelyRepeated(RepeatedBodyWrite {
            project: self.hir.identity(),
            evidence: self.evidence_binding.clone(),
            target: key.clone(),
            sites,
        }))
    }

    fn possible_write_blockers(
        &self,
        key: &AccessKey,
        facts: &WriteFacts,
        may_repeat: &BTreeSet<AccessKey>,
        uncertain: &[UncertainWrite],
    ) -> BTreeSet<FactBlocker> {
        let mut blockers = BTreeSet::new();
        if may_repeat.contains(key) {
            let sites = self.repeat_sites(facts, key);
            if sites.is_empty() {
                blockers.insert(FactBlocker::WitnessWrite(
                    self.cfg.exit(),
                    WitnessWriteIssue::PossibleRepeat,
                ));
            }
            for site in sites {
                blockers.insert(FactBlocker::WitnessWrite(site, WitnessWriteIssue::PossibleRepeat));
            }
        }
        for write in uncertain {
            if write.may_alias(key) {
                blockers.extend(write.blockers.iter().cloned());
                blockers.insert(FactBlocker::WitnessWrite(
                    write.site,
                    WitnessWriteIssue::UnresolvedTarget,
                ));
            }
        }
        blockers
    }

    fn repeat_sites(&self, facts: &WriteFacts, key: &AccessKey) -> BTreeSet<NodeId> {
        let mut sites = BTreeSet::new();
        for site in self.cfg.nodes() {
            let Some(node) = self.cfg.node(*site) else { continue };
            let CfgNodeKind::Witness { target, .. } = &node.kind else { continue };
            if self.exact_access_key(target).certified() != Some(key) {
                continue;
            }
            let Some(WriteState::Reached { may_written, .. }) =
                facts.get(site).and_then(|item| item.input.as_ref())
            else {
                continue;
            };
            if may_written.contains(key) {
                sites.insert(*site);
            }
        }
        sites
    }

    /// A duplicate on every reachable path invalidates the whole template body.
    pub(crate) fn definitely_repeats_any_body_write(&self) -> Fact<bool> {
        let (facts, _) = match self.solve_body_writes() {
            Ok(result) => result,
            Err(blockers) => return Fact::blocked(blockers),
        };
        let Some(WriteState::Reached { must_repeat_any, .. }) =
            facts.get(&self.cfg.exit()).and_then(|item| item.output.as_ref())
        else {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        };
        Fact::known(*must_repeat_any)
    }

    fn solve_body_writes(
        &self,
    ) -> Result<(WriteFacts, Vec<UncertainWrite>), BTreeSet<FactBlocker>> {
        const WRITE_UPDATE_BUDGET: usize = 100_000;
        let mut exact_writes = BTreeMap::new();
        let mut uncertain = Vec::new();
        for site in self.cfg.nodes() {
            if self.reachable_node(*site).certified() == Some(&false) {
                continue;
            }
            let Some(node) = self.cfg.node(*site) else { continue };
            self.classify_write(*site, &node.kind, &mut exact_writes, &mut uncertain);
        }
        let analysis = WriteAnalysis {
            exact_writes,
            pruned: forward_pruned_edges(
                self.hir,
                self.cfg.as_ref(),
                self.field,
                &self.forward,
                self.calls.as_deref(),
            ),
        };
        let result =
            solve::<_, _, Forward>(self.cfg.as_ref(), &analysis, Some(WRITE_UPDATE_BUDGET))
                .map_err(|_| BTreeSet::from([FactBlocker::ForeignQuery]))?;
        match result {
            SolveResult::Complete(facts) => Ok((facts, uncertain)),
            SolveResult::Incomplete { blockers, .. } => {
                Err(blockers.iter().map(FactBlocker::from).collect())
            }
        }
    }

    fn classify_write(
        &self,
        site: NodeId,
        kind: &CfgNodeKind,
        exact: &mut BTreeMap<NodeId, AccessKey>,
        uncertain: &mut Vec<UncertainWrite>,
    ) {
        let path = match kind {
            CfgNodeKind::Witness { target, .. } => target,
            CfgNodeKind::OpaqueAssignment { target, operator, .. }
                if witness_operator(*operator) =>
            {
                uncertain.push(UncertainWrite {
                    site,
                    may_target: Some(key_for_path(self.hir, self.field, target, &BTreeMap::new())),
                    blockers: BTreeSet::new(),
                });
                return;
            }
            CfgNodeKind::Opaque(_) => {
                uncertain.push(UncertainWrite {
                    site,
                    may_target: None,
                    blockers: BTreeSet::new(),
                });
                return;
            }
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::Evaluate(_)
            | CfgNodeKind::LoopHeader
            | CfgNodeKind::Branch { .. }
            | CfgNodeKind::Constraint { .. }
            | CfgNodeKind::Assignment { .. }
            | CfgNodeKind::DeferredAssignment { .. }
            | CfgNodeKind::Update { .. }
            | CfgNodeKind::Instantiate { .. }
            | CfgNodeKind::OpaqueAssignment { .. }
            | CfgNodeKind::OpaqueEquality { .. }
            | CfgNodeKind::Declaration { .. }
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Assert { .. }
            | CfgNodeKind::DeferredAssert { .. }
            | CfgNodeKind::Log => return,
        };
        let key = self.exact_access_key(path);
        if let Some(key) = key.certified() {
            exact.insert(site, key.clone());
        } else {
            uncertain.push(UncertainWrite {
                site,
                may_target: Some(key_for_path(self.hir, self.field, path, &BTreeMap::new())),
                blockers: key.unavailable().cloned().unwrap_or_default(),
            });
        }
    }
}

fn witness_operator(operator: AssignmentOperator) -> bool {
    match operator {
        AssignmentOperator::Witness
        | AssignmentOperator::ReverseWitness
        | AssignmentOperator::Constraint
        | AssignmentOperator::ReverseConstraint => true,
        AssignmentOperator::Assign
        | AssignmentOperator::Add
        | AssignmentOperator::Subtract
        | AssignmentOperator::Multiply
        | AssignmentOperator::Divide
        | AssignmentOperator::IntegerDivide
        | AssignmentOperator::Modulo
        | AssignmentOperator::Power
        | AssignmentOperator::ShiftLeft
        | AssignmentOperator::ShiftRight
        | AssignmentOperator::BitAnd
        | AssignmentOperator::BitOr
        | AssignmentOperator::BitXor => false,
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use abstract_interpretation::lattice::Lattice;
    use parser::hir::lift_project;
    use parser::new_frontend::{load_sources, Version, VersionPolicy};

    use crate::hir_facts::AccessKey;
    use crate::hir_facts::write_validity::WriteState;

    fn keys() -> (AccessKey, AccessKey) {
        let source = "template T(){signal output x;signal output y;}";
        let directory = std::env::temp_dir().join(format!(
            "circomspect-write-domain-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("case.circom");
        fs::write(&path, source).unwrap();
        let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let symbols = lifted.hir.symbols();
        let x = symbols.iter().find(|item| item.name == "x").unwrap().id;
        let y = symbols.iter().find(|item| item.name == "y").unwrap().id;
        (
            AccessKey { root: x, instance: None, steps: vec![] },
            AccessKey { root: y, instance: None, steps: vec![] },
        )
    }

    #[test]
    fn write_domain_join_laws_and_transfer_monotonicity() {
        let (x, y) = keys();
        let mut x_once = WriteState::empty();
        x_once.write(&x);
        let mut x_twice = x_once.clone();
        x_twice.write(&x);
        let mut y_once = WriteState::empty();
        y_once.write(&y);
        let mut both_once = x_once.clone();
        both_once.write(&y);
        let mut y_twice = y_once.clone();
        y_twice.write(&y);
        let mut branch = x_once.clone();
        branch.join_assign(&y_once);
        let states = [
            WriteState::Unreachable,
            WriteState::empty(),
            x_once,
            x_twice,
            y_once,
            y_twice,
            both_once,
            branch,
        ];
        for left in &states {
            assert!(left.leq(left));
            for right in &states {
                let mut joined = left.clone();
                joined.join_assign(right);
                assert!(left.leq(&joined));
                assert!(right.leq(&joined));
                let mut reverse = right.clone();
                reverse.join_assign(left);
                assert_eq!(joined, reverse);
                if left.leq(right) {
                    let mut left_after = left.clone();
                    let mut right_after = right.clone();
                    left_after.write(&x);
                    right_after.write(&x);
                    assert!(left_after.leq(&right_after));
                }
                for upper in &states {
                    if left.leq(upper) && right.leq(upper) {
                        assert!(joined.leq(upper));
                    }
                }
                for third in &states {
                    let mut grouped = joined.clone();
                    grouped.join_assign(third);
                    let mut right_joined = right.clone();
                    right_joined.join_assign(third);
                    let mut alternate = left.clone();
                    alternate.join_assign(&right_joined);
                    assert_eq!(grouped, alternate);
                }
            }
        }
    }
}
