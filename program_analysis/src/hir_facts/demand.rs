//! Backward observable demand for safely removable scalar assignments.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{EdgeId, FlowGraph, NodeId};
use abstract_interpretation::lattice::Lattice;
use abstract_interpretation::solver::{DataflowAnalysis, SolveResult, Transfer, TransferOutcome};
use parser::hir::{AccessPath, DefinitionRef, Effect, ExprId, ExprKind, HirProject, SymbolKind};
use parser::new_frontend::{AssignmentOperator, Span};

use crate::hir_cfg::{Constraint, CfgEdge, CfgNode, CfgNodeKind, DefinitionCfg};
use crate::hir_facts::access::{key_for_path, AccessKey};
use crate::hir_facts::purity::ScalarEvaluationSafety;
use crate::hir_facts::{AnalysisFacts, Fact, FactBlocker, FieldContext, VisitAccesses};
use crate::interprocedural::{CallContext, ContextEvidence};
use crate::scalar_evidence::ScalarExpressionEvidence;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum DemandState {
    Unreachable,
    Reached(BTreeSet<AccessKey>),
}

impl DemandState {
    pub(crate) fn demands(&self, query: &AccessKey) -> Option<bool> {
        let Self::Reached(keys) = self else { return None };
        Some(keys.iter().any(|key| key.may_alias(query)))
    }
}

impl Lattice for DemandState {
    fn bottom() -> Self {
        Self::Unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unreachable, _) => true,
            (Self::Reached(_), Self::Unreachable) => false,
            (Self::Reached(left), Self::Reached(right)) => left.is_subset(right),
        }
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        match (&mut *self, other) {
            (Self::Unreachable | Self::Reached(_), Self::Unreachable) => false,
            (state @ Self::Unreachable, Self::Reached(_)) => {
                *state = other.clone();
                true
            }
            (Self::Reached(left), Self::Reached(right)) => {
                let before = left.len();
                left.extend(right.iter().cloned());
                left.len() != before
            }
        }
    }
}

pub(crate) struct DemandAnalysis<'a> {
    hir: &'a HirProject,
    field: &'a FieldContext,
    calls: Option<&'a ScalarExpressionEvidence>,
    pruned_edges: BTreeSet<EdgeId>,
    resolved_deferred: BTreeSet<NodeId>,
    scalar_evaluation_safety: ScalarEvaluationSafety,
}

impl<'a> DemandAnalysis<'a> {
    pub(crate) fn new(
        hir: &'a HirProject,
        field: &'a FieldContext,
        pruned_edges: BTreeSet<EdgeId>,
    ) -> Self {
        Self {
            hir,
            field,
            calls: None,
            pruned_edges,
            resolved_deferred: BTreeSet::new(),
            scalar_evaluation_safety: ScalarEvaluationSafety::default(),
        }
    }

    pub(crate) fn with_calls(mut self, calls: Option<&'a ScalarExpressionEvidence>) -> Self {
        self.calls = calls;
        self
    }

    pub(crate) fn with_resolved_deferred(mut self, nodes: BTreeSet<NodeId>) -> Self {
        self.resolved_deferred = nodes;
        self
    }

    pub(super) fn with_scalar_evaluation_safety(mut self, safety: ScalarEvaluationSafety) -> Self {
        self.scalar_evaluation_safety = safety;
        self
    }

    fn pure_scalar_assignment(&self, target: &AccessPath, value: ExprId) -> bool {
        pure_scalar_assignment(self.hir, target, value, self.calls, &self.scalar_evaluation_safety)
    }

    fn removable_call(&self, expression: ExprId) -> bool {
        self.calls.is_some_and(|calls| calls.removable_call(expression))
    }

    fn collect(&self, expression: ExprId, keys: &mut BTreeSet<AccessKey>) -> bool {
        expression.visit_accesses_with(self.hir, &|id| self.removable_call(id), &mut |path| {
            keys.insert(key_for_path(self.hir, self.field, path, &BTreeMap::new()));
        })
    }

    fn collect_path(&self, path: &AccessPath, keys: &mut BTreeSet<AccessKey>) -> bool {
        path.visit_accesses_with(self.hir, &|id| self.removable_call(id), &mut |read| {
            keys.insert(key_for_path(self.hir, self.field, read, &BTreeMap::new()));
        })
    }

    fn transfer_assignment(
        &self,
        target: &AccessPath,
        value: ExprId,
        operator: AssignmentOperator,
        keys: &mut BTreeSet<AccessKey>,
    ) -> bool {
        if operator != AssignmentOperator::Assign || !self.pure_scalar_assignment(target, value) {
            return self.collect_path(target, keys) && self.collect(value, keys);
        }
        let key = key_for_path(self.hir, self.field, target, &BTreeMap::new());
        let demanded = keys.iter().any(|candidate| candidate.may_alias(&key));
        keys.remove(&key);
        !demanded || self.collect(value, keys)
    }

    fn collect_log(&self, node: &CfgNode, keys: &mut BTreeSet<AccessKey>) -> bool {
        let Some(origin) = node.origin else { return false };
        let Some(block) = self.hir.block(origin.block) else { return false };
        let Some(Effect::Log { values, .. }) = block.effects.get(origin.effect_index) else {
            return false;
        };
        values.iter().all(|value| self.collect(*value, keys))
    }

    fn collect_evaluation(&self, expression: ExprId, keys: &mut BTreeSet<AccessKey>) -> bool {
        let Some(expr) = self.hir.expression(expression) else { return false };
        if pure_scalar_value(
            self.hir,
            &expr.kind,
            expression,
            self.calls,
            &self.scalar_evaluation_safety,
        ) {
            return true;
        }
        self.collect(expression, keys)
    }

    fn collect_dimensions(
        &self,
        symbol: parser::hir::SymbolId,
        keys: &mut BTreeSet<AccessKey>,
    ) -> bool {
        let Some(symbol) = self.hir.symbol(symbol) else { return false };
        symbol.dimensions.iter().all(|dimension| self.collect(*dimension, keys))
    }

    fn transfer_local(&self, node: &CfgNode, keys: &mut BTreeSet<AccessKey>) -> bool {
        if let CfgNodeKind::Evaluate(expression) = &node.kind {
            return self.collect_evaluation(*expression, keys);
        }
        if let CfgNodeKind::Assignment { target, value, operator } = &node.kind {
            return self.transfer_assignment(target, *value, *operator, keys);
        }
        if let CfgNodeKind::DeferredAssignment { target, value, operator } = &node.kind {
            return self.resolved_deferred.contains(&node.id)
                && self.pure_scalar_assignment(target, *value)
                && self.transfer_assignment(target, *value, *operator, keys);
        }
        if let CfgNodeKind::Declaration { symbol } = &node.kind {
            keys.retain(|key| key.root != *symbol);
            return self.collect_dimensions(*symbol, keys);
        }
        self.collect_log(node, keys)
    }

    fn transfer_observation(&self, node: &CfgNode, keys: &mut BTreeSet<AccessKey>) -> bool {
        if let CfgNodeKind::Constraint(constraint) = &node.kind {
            return match constraint {
                Constraint::Assignment { target, value } => {
                    self.collect_path(target, keys) && self.collect(*value, keys)
                }
                Constraint::Equality { left, right } => {
                    let right_complete = self.collect(*right, keys);
                    self.collect(*left, keys) && right_complete
                }
            };
        }
        if let CfgNodeKind::Branch { condition, .. }
        | CfgNodeKind::Assert { condition }
        | CfgNodeKind::DeferredAssert { condition } = &node.kind
        {
            return self.collect(*condition, keys);
        }
        let CfgNodeKind::Return(value) = &node.kind else { return false };
        self.collect(*value, keys)
    }

    fn transfer_effect(&self, node: &CfgNode, keys: &mut BTreeSet<AccessKey>) -> bool {
        let (CfgNodeKind::Witness { target, value } | CfgNodeKind::Instantiate { target, value }) =
            &node.kind
        else {
            return false;
        };
        self.collect_path(target, keys) && self.collect(*value, keys)
    }
}

impl DataflowAnalysis<DefinitionCfg> for DemandAnalysis<'_> {
    type State = DemandState;
    type Reason = String;

    fn boundary(&self, _: NodeId) -> Self::State {
        DemandState::Reached(BTreeSet::new())
    }
}

impl Transfer<DemandAnalysis<'_>, DemandState, String> for CfgNode {
    fn apply(
        &self,
        analysis: &DemandAnalysis<'_>,
        input: &DemandState,
    ) -> TransferOutcome<DemandState, String> {
        let mut output = input.clone();
        let DemandState::Reached(keys) = &mut output else { return TransferOutcome::Known(output) };
        let complete = match &self.kind {
            CfgNodeKind::Evaluate(_)
            | CfgNodeKind::Assignment { .. }
            | CfgNodeKind::DeferredAssignment { .. }
            | CfgNodeKind::Declaration { .. }
            | CfgNodeKind::Log => analysis.transfer_local(self, keys),
            CfgNodeKind::Constraint(_)
            | CfgNodeKind::Branch { .. }
            | CfgNodeKind::Assert { .. }
            | CfgNodeKind::DeferredAssert { .. }
            | CfgNodeKind::Return(_) => analysis.transfer_observation(self, keys),
            CfgNodeKind::Witness { .. } | CfgNodeKind::Instantiate { .. } => {
                analysis.transfer_effect(self, keys)
            }
            CfgNodeKind::Entry | CfgNodeKind::Exit | CfgNodeKind::LoopHeader => true,
            CfgNodeKind::Update { .. }
            | CfgNodeKind::OpaqueAssignment { .. }
            | CfgNodeKind::OpaqueEquality { .. }
            | CfgNodeKind::Opaque(_) => false,
        };
        if complete {
            TransferOutcome::Known(output)
        } else {
            TransferOutcome::Opaque {
                provisional: output,
                reason: "unresolved observable demand".into(),
            }
        }
    }
}

impl Transfer<DemandAnalysis<'_>, DemandState, String> for CfgEdge {
    fn apply(
        &self,
        analysis: &DemandAnalysis<'_>,
        input: &DemandState,
    ) -> TransferOutcome<DemandState, String> {
        if analysis.pruned_edges.contains(&self.id) {
            TransferOutcome::Known(DemandState::Unreachable)
        } else {
            TransferOutcome::Known(input.clone())
        }
    }
}

fn pure_scalar_assignment(
    hir: &HirProject,
    target: &AccessPath,
    value: ExprId,
    calls: Option<&ScalarExpressionEvidence>,
    safety: &ScalarEvaluationSafety,
) -> bool {
    let Some(symbol) = hir.symbol(target.root) else { return false };
    if symbol.kind != SymbolKind::Variable || symbol.rank != 0 || !target.steps.is_empty() {
        return false;
    }
    let Some(expression) = hir.expression(value) else { return false };
    pure_scalar_value(hir, &expression.kind, value, calls, safety)
}

fn pure_scalar_value(
    hir: &HirProject,
    kind: &ExprKind,
    expression: ExprId,
    calls: Option<&ScalarExpressionEvidence>,
    safety: &ScalarEvaluationSafety,
) -> bool {
    match kind {
        ExprKind::Number(_) => true,
        ExprKind::Access(path) => {
            let Some(symbol) = hir.symbol(path.root) else { return false };
            (symbol.kind == SymbolKind::Variable
                || (symbol.kind == SymbolKind::Parameter && safety.contains(expression)))
                && symbol.rank == 0
                && path.steps.is_empty()
                && !path.component_input
                && !path.component_output
        }
        ExprKind::Call { .. } => calls.is_some_and(|calls| calls.removable_call(expression)),
        ExprKind::Unary { .. } | ExprKind::Binary { .. } => safety.contains(expression),
        ExprKind::Array(_)
        | ExprKind::Tuple(_)
        | ExprKind::AnonymousComponent { .. }
        | ExprKind::Ternary { .. }
        | ExprKind::Parallel(_)
        | ExprKind::Opaque(_) => false,
    }
}

/// Source-bound proof that one safely removable assignment has no observable demand.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UnobservedAssignment {
    evidence: ContextEvidence,
    node: NodeId,
    span: Span,
}

impl UnobservedAssignment {
    #[must_use]
    pub fn definition(&self) -> DefinitionRef {
        self.evidence.context().definition()
    }

    #[must_use]
    pub fn context(&self) -> &CallContext {
        self.evidence.context()
    }

    #[must_use]
    pub fn node(&self) -> NodeId {
        self.node
    }

    #[must_use]
    pub fn span(&self) -> Span {
        self.span
    }
}

/// Certified status of one exact scalar assignment's observable value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssignmentDemand {
    MayBeObserved,
    Unobserved(UnobservedAssignment),
}

pub(crate) fn unobserved(evidence: &ContextEvidence, node: NodeId, span: Span) -> AssignmentDemand {
    AssignmentDemand::Unobserved(UnobservedAssignment { evidence: evidence.clone(), node, span })
}

impl AnalysisFacts<'_> {
    /// Prove demand for one exact, safely removable scalar assignment in this CFG.
    ///
    /// The result is a local fact. A warning also needs provider validation of
    /// the active source and execution scope.
    pub(crate) fn assignment_demand(
        &self,
        id: NodeId,
        target: &AccessPath,
        evidence: &ContextEvidence,
    ) -> Fact<AssignmentDemand> {
        if !self.matches_evidence(evidence) {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        let Some(node) = self.cfg.node(id) else {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        let (CfgNodeKind::Assignment { target: written, value, operator }
        | CfgNodeKind::DeferredAssignment { target: written, value, operator }) = &node.kind
        else {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        if written != target {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        let resolved = if let CfgNodeKind::DeferredAssignment { .. } = &node.kind {
            self.resolved_deferred_assignment(id)
        } else {
            true
        };
        if *operator != AssignmentOperator::Assign
            || !pure_scalar_assignment(
                self.hir,
                target,
                *value,
                self.calls.as_deref(),
                &self.scalar_evaluation_safety,
            )
            || !resolved
        {
            return Fact::blocked(BTreeSet::from([FactBlocker::OpaqueNode(
                id,
                "assignment is not safely removable".into(),
            )]));
        }
        self.certified_assignment_demand(id, written, evidence)
    }

    fn certified_assignment_demand(
        &self,
        id: NodeId,
        target: &AccessPath,
        evidence: &ContextEvidence,
    ) -> Fact<AssignmentDemand> {
        let reachable = self.reachable_node(id);
        match reachable.certified() {
            Some(true) => {}
            Some(false) => return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit])),
            None => return Fact::blocked(reachable.unavailable().cloned().unwrap_or_default()),
        }
        let forward = self.forward_completion_blockers();
        if !forward.is_empty() {
            return Fact::blocked(forward);
        }
        let SolveResult::Complete(facts) = &self.demand else {
            return Fact::blocked(self.demand_blockers());
        };
        let Some(state) = facts.get(&id).and_then(|facts| facts.output.as_ref()) else {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        };
        let key = key_for_path(self.hir, self.field, target, &BTreeMap::new());
        match state.demands(&key) {
            Some(true) => Fact::known(AssignmentDemand::MayBeObserved),
            Some(false) => Fact::known(unobserved(evidence, id, target.span)),
            None => Fact::blocked(BTreeSet::from([FactBlocker::MissingExit])),
        }
    }

    fn demand_blockers(&self) -> BTreeSet<FactBlocker> {
        let SolveResult::Incomplete { blockers, .. } = &self.demand else {
            return BTreeSet::new();
        };
        let mut reasons = BTreeSet::new();
        for blocker in blockers {
            reasons.insert(FactBlocker::from(blocker));
        }
        if reasons.is_empty() {
            reasons.insert(FactBlocker::MissingExit);
        }
        reasons
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};
    use std::fs;

    use abstract_interpretation::graph::FlowGraph;
    use abstract_interpretation::lattice::Lattice;
    use abstract_interpretation::solver::{Transfer, TransferOutcome};
    use parser::hir::lift_project;
    use parser::new_frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::{build_cfg, CfgNodeKind};
    use crate::hir_facts::access::key_for_path;
    use crate::hir_facts::demand::{DemandAnalysis, DemandState};
    use crate::hir_facts::FieldContext;
    use crate::interprocedural::ProjectSummaries;

    #[test]
    fn production_assignment_transfer_is_monotone_over_finite_demand_states() {
        let directory =
            std::env::temp_dir().join(format!("circomspect-demand-law-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(&source, "function Check(){var x=1;var y=x;return 7;}").unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lift_project(&loaded).hir;
        let cfg = build_cfg(&hir, hir.definition("Check").unwrap()).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let mut keys = Vec::new();
        let mut assignment = None;
        for id in cfg.nodes() {
            let Some(node) = cfg.node(*id) else { continue };
            let CfgNodeKind::Assignment { target, .. } = &node.kind else { continue };
            keys.push(key_for_path(&hir, &field, target, &BTreeMap::new()));
            if hir.symbol(target.root).is_some_and(|symbol| symbol.name == "y") {
                assignment = Some(node);
            }
        }
        assert_eq!(keys.len(), 2);
        let assignment = assignment.unwrap();
        let mut states = vec![DemandState::Unreachable];
        for mask in 0..4_u8 {
            let mut demanded = BTreeSet::new();
            for (index, key) in keys.iter().enumerate() {
                if mask & (1 << index) != 0 {
                    demanded.insert(key.clone());
                }
            }
            states.push(DemandState::Reached(demanded));
        }
        let analysis = DemandAnalysis::new(&hir, &field, BTreeSet::new());
        for left in &states {
            for right in &states {
                let mut joined = left.clone();
                let changed = joined.join_assign(right);
                assert_eq!(changed, joined != *left);
                assert!(left.leq(&joined) && right.leq(&joined));
                let mut reverse = right.clone();
                reverse.join_assign(left);
                assert_eq!(joined, reverse);
                for third in &states {
                    let mut first = joined.clone();
                    first.join_assign(third);
                    let mut right_then_third = right.clone();
                    right_then_third.join_assign(third);
                    let mut alternative = left.clone();
                    alternative.join_assign(&right_then_third);
                    assert_eq!(first, alternative);
                }
                if !left.leq(right) {
                    continue;
                }
                let TransferOutcome::Known(left_result) = assignment.apply(&analysis, left) else {
                    panic!("scalar transfer must be known")
                };
                let TransferOutcome::Known(right_result) = assignment.apply(&analysis, right)
                else {
                    panic!("scalar transfer must be known")
                };
                assert!(left_result.leq(&right_result));
            }
        }
    }

    #[test]
    fn provider_proven_scalar_transfers_are_monotone() {
        for source in [
            "function Pure(n){return n;}function Check(){var x=1;var y=Pure(x);return 7;}",
            "function Check(){var x=1;var y=-(x+2);return 7;}",
        ] {
            assert_scalar_transfer_monotone(source);
        }
    }

    fn assert_scalar_transfer_monotone(source: &str) {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-demand-pure-law-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("case.circom");
        fs::write(&path, source).unwrap();
        let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("Check").unwrap();
        let evidence = provider.symbolic_root(definition).unwrap();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let assignment = facts.cfg().nodes().iter().find_map(|id| {
            let node = facts.cfg().node(*id)?;
            let (CfgNodeKind::Assignment { target, .. }
            | CfgNodeKind::DeferredAssignment { target, .. }) = &node.kind
            else {
                return None;
            };
            (lifted.hir.symbol(target.root)?.name == "y").then_some(node)
        });
        let Some(assignment) = assignment else { panic!("pure call assignment must exist") };
        let (CfgNodeKind::Assignment { target, .. }
        | CfgNodeKind::DeferredAssignment { target, .. }) = &assignment.kind
        else {
            panic!("selected node must remain an assignment")
        };
        let field = FieldContext::for_curve(Curve::Bn254);
        let key = key_for_path(&lifted.hir, &field, target, &BTreeMap::new());
        let analysis = DemandAnalysis::new(&lifted.hir, &field, BTreeSet::new())
            .with_calls(facts.calls.as_deref())
            .with_scalar_evaluation_safety(facts.scalar_evaluation_safety.clone())
            .with_resolved_deferred(facts.resolved_deferred.clone());
        let states = [
            DemandState::Unreachable,
            DemandState::Reached(BTreeSet::new()),
            DemandState::Reached(BTreeSet::from([key])),
        ];
        for left in &states {
            for right in &states {
                if !left.leq(right) {
                    continue;
                }
                let TransferOutcome::Known(left_result) = assignment.apply(&analysis, left) else {
                    panic!("proven pure call transfer must be known")
                };
                let TransferOutcome::Known(right_result) = assignment.apply(&analysis, right)
                else {
                    panic!("proven pure call transfer must be known")
                };
                assert!(left_result.leq(&right_result));
            }
        }
    }
}
