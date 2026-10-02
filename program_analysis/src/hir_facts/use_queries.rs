//! Queries over certified backward liveness for assignments and parameters.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{FlowGraph, NodeId};
use abstract_interpretation::solver::SolveResult;
use parser::hir::{AccessPath, DefinitionRef, SymbolId, SymbolKind};

use crate::hir_cfg::CfgNodeKind;

use crate::hir_facts::access::key_for_path;
use crate::hir_facts::liveness::LiveState;
use crate::hir_facts::{AnalysisFacts, Fact, FactBlocker, VisitAccesses};

pub(super) enum ReadScope {
    Handle,
    Parameter,
}

impl AnalysisFacts<'_> {
    /// Whether an assigned access may be read after this reachable CFG node.
    ///
    /// A false result needs the same complete backward evidence as `live_before`.
    /// Callers must establish that `node` actually writes `path` before using
    /// the result to describe a dead assigned value.
    pub fn live_after(&self, node: NodeId, path: &AccessPath) -> Fact<bool> {
        if self.cfg.node(node).is_none() {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        let blockers = self.backward_blockers(path);
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        let facts = match &self.backward {
            SolveResult::Complete(facts) => facts.get(&node),
            SolveResult::Incomplete { provisional_facts, .. } => provisional_facts.get(&node),
        };
        let Some(state) = facts.and_then(|facts| facts.output.as_ref()) else {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        };
        let key = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        match state.contains_alias(&key) {
            Some(read) => Fact::known(read),
            None => Fact::blocked(BTreeSet::from([FactBlocker::MissingExit])),
        }
    }

    /// Whether any reachable expression can read this declared parameter.
    ///
    /// This scans all certified backward sites. Entry liveness alone misses a
    /// read after a parameter overwrite, so it cannot establish this claim.
    pub fn parameter_read(&self, parameter: SymbolId) -> Fact<bool> {
        let Some(symbol) = self.hir.symbol(parameter) else {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        if symbol.kind != SymbolKind::Parameter || !self.parameters().contains(&parameter) {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignDefinition]));
        }
        let path = AccessPath {
            root: parameter,
            steps: Vec::new(),
            terminal: parameter,
            component_input: false,
            component_output: false,
            span: symbol.span,
        };
        self.read_path(&path, ReadScope::Parameter)
    }

    fn parameters(&self) -> &[SymbolId] {
        match self.cfg.definition() {
            DefinitionRef::Function(id) => {
                self.hir.function(id).map_or(&[], |definition| definition.parameters.as_slice())
            }
            DefinitionRef::Template(id) => {
                self.hir.template(id).map_or(&[], |definition| definition.parameters.as_slice())
            }
            DefinitionRef::Bus(id) => {
                self.hir.bus(id).map_or(&[], |definition| definition.parameters.as_slice())
            }
        }
    }

    pub(super) fn read_path(&self, path: &AccessPath, scope: ReadScope) -> Fact<bool> {
        let blockers = self.read_blockers(path, &scope);
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        if let SolveResult::Incomplete { .. } = &self.backward {
            if let ReadScope::Handle = scope {
                return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
            }
        }
        let key = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        let mut observed = false;
        for node in self.cfg.nodes() {
            let Some(state) = self.backward_input(*node) else {
                continue;
            };
            let Some(read) = state.contains_alias(&key) else {
                continue;
            };
            observed = true;
            if read {
                return Fact::known(true);
            }
        }
        if observed {
            Fact::known(false)
        } else {
            Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]))
        }
    }

    fn read_blockers(&self, path: &AccessPath, scope: &ReadScope) -> BTreeSet<FactBlocker> {
        let mut blockers = self.backward_blockers_query(path, true);
        if let ReadScope::Parameter = scope {
            blockers.remove(&FactBlocker::AggregateAccess);
            blockers.retain(|blocker| match blocker {
                FactBlocker::OpaqueNode(node, _) => self.opaque_read_relevant(*node, path),
                FactBlocker::Budget(_)
                | FactBlocker::OpaqueEdge(_, _)
                | FactBlocker::ExternalSummary
                | FactBlocker::AggregateAccess
                | FactBlocker::DeferredShape(_)
                | FactBlocker::AggregateConstraint(_)
                | FactBlocker::DeferredControl(_)
                | FactBlocker::OpaqueExpression(_)
                | FactBlocker::UnsupportedRelation(_)
                | FactBlocker::WitnessWrite(_, _)
                | FactBlocker::SignalRead(_, _)
                | FactBlocker::MissingExit
                | FactBlocker::ForeignQuery
                | FactBlocker::ForeignDefinition => true,
            });
        }
        blockers
    }

    fn backward_input(&self, node: NodeId) -> Option<&LiveState> {
        match &self.backward {
            SolveResult::Complete(facts) => facts.get(&node).and_then(|facts| facts.input.as_ref()),
            SolveResult::Incomplete { provisional_facts, .. } => {
                provisional_facts.get(&node).and_then(|facts| facts.input.as_ref())
            }
        }
    }

    fn opaque_read_relevant(&self, node: NodeId, path: &AccessPath) -> bool {
        let Some(node) = self.cfg.node(node) else { return true };
        let query = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        let mut relevant = false;
        let mut inspect = |used: &AccessPath| {
            relevant |=
                key_for_path(self.hir, self.field, used, &BTreeMap::new()).may_alias(&query);
        };
        let complete = match &node.kind {
            CfgNodeKind::Assignment { target, value, .. } => {
                let target_complete = target.visit_accesses(self.hir, &mut inspect);
                target_complete && value.visit_accesses(self.hir, &mut inspect)
            }
            CfgNodeKind::Update { target, .. } => target.visit_accesses(self.hir, &mut inspect),
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::Evaluate(_)
            | CfgNodeKind::LoopHeader
            | CfgNodeKind::Branch { .. }
            | CfgNodeKind::Witness { .. }
            | CfgNodeKind::Constraint { .. }
            | CfgNodeKind::DeferredAssignment { .. }
            | CfgNodeKind::Instantiate { .. }
            | CfgNodeKind::OpaqueAssignment { .. }
            | CfgNodeKind::OpaqueEquality { .. }
            | CfgNodeKind::Declaration { .. }
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Assert { .. }
            | CfgNodeKind::DeferredAssert { .. }
            | CfgNodeKind::Log
            | CfgNodeKind::Opaque(_) => false,
        };
        !complete || relevant
    }
}
