//! Required evaluation can precede an assignment whose value remains opaque.

use std::collections::BTreeSet;

use abstract_interpretation::graph::{EdgeId, FlowGraph, NodeId};

use crate::hir_cfg::{CfgNodeKind, EdgeKind};
use crate::hir_facts::{AnalysisFacts, Fact, FactBlocker, Range, VisitAccesses};

impl AnalysisFacts<'_> {
    /// Prove evaluation is necessary on every successful entry-to-exit completion.
    /// Unavailable guards keep both paths. Typed value effects may themselves fail;
    /// this certificate cannot prove that preceding effects complete or produce a value.
    pub(crate) fn required_evaluation(&self, node: NodeId) -> Fact<bool> {
        let reachable = self.reachable_for_completion(node);
        if reachable.certified() != Some(&true) {
            return reachable;
        }
        Fact::known(!self.path_bypasses(node, &self.certified_guard_edges()))
    }

    fn reachable_for_completion(&self, node: NodeId) -> Fact<bool> {
        if self.cfg.node(node).is_none() {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        if self.certified_dead_node(node) {
            return Fact::known(false);
        }
        let mut blockers = self.reachability_blockers(&BTreeSet::from([node]));
        blockers.retain(|blocker| match blocker {
            FactBlocker::OpaqueNode(id, _) => !self.typed_value_effect(*id),
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
            | FactBlocker::MissingExit
            | FactBlocker::ForeignQuery
            | FactBlocker::ForeignDefinition => true,
        });
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        Fact::known(self.site_state(node).is_some_and(|state| state.variables().is_some()))
    }

    fn typed_value_effect(&self, node: NodeId) -> bool {
        let Some(node) = self.cfg.node(node) else { return false };
        match &node.kind {
            CfgNodeKind::Evaluate(expression) => expression.visit_accesses(self.hir, &mut |_| {}),
            CfgNodeKind::Assignment { .. }
            | CfgNodeKind::DeferredAssignment { .. }
            | CfgNodeKind::OpaqueAssignment { .. }
            | CfgNodeKind::Update { .. } => true,
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::LoopHeader
            | CfgNodeKind::Branch { .. }
            | CfgNodeKind::Witness { .. }
            | CfgNodeKind::Constraint { .. }
            | CfgNodeKind::Instantiate { .. }
            | CfgNodeKind::Declaration { .. }
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Assert { .. }
            | CfgNodeKind::DeferredAssert { .. }
            | CfgNodeKind::Log
            | CfgNodeKind::Opaque(_)
            | CfgNodeKind::OpaqueEquality { .. } => false,
        }
    }

    fn certified_guard_edges(&self) -> BTreeSet<EdgeId> {
        let mut pruned = BTreeSet::new();
        for id in self.cfg.edges() {
            if self.certified_false_edge(*id) {
                pruned.insert(*id);
            }
        }
        pruned
    }

    fn certified_false_edge(&self, id: EdgeId) -> bool {
        let Some(edge) = self.cfg.edge(id) else { return false };
        let Some(CfgNodeKind::Branch { condition, .. }) =
            self.cfg.node(edge.source).map(|node| &node.kind)
        else {
            return false;
        };
        let condition = self.range(*condition);
        let Some(Range::Exact(condition)) = condition.certified() else { return false };
        let truth = !self.field.is_zero(condition);
        match edge.payload.kind {
            EdgeKind::True => !truth,
            EdgeKind::False => truth,
            EdgeKind::Normal | EdgeKind::Loop | EdgeKind::Return => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use abstract_interpretation::graph::FlowGraph;
    use parser::hir::{lift_project, ExprKind};
    use parser::new_frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::{build_cfg, CfgNodeKind};
    use crate::hir_facts::{analyze, FieldContext};

    #[test]
    fn pending_alternatives_and_back_edges_cannot_prove_required_evaluation() {
        for branch in ["if(condition){choice=0;}", "while(condition){choice=0;}"] {
            let source = format!(
                "function F(){{return 7;}} \
                 template T(){{signal input condition;var choice=1;{branch}\
                 var value=choice?F():7;}}"
            );
            assert_not_required_at_any_budget(&source);
        }
    }

    fn assert_not_required_at_any_budget(source: &str) {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-required-evaluation-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let path = directory.join("case.circom");
        std::fs::write(&path, source).unwrap();
        let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        assert!(lifted.syntax_diagnostics.is_empty());
        let definition = lifted.hir.definition("T").unwrap();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let field = FieldContext::for_curve(Curve::Bn254);
        let mut calls = Vec::new();
        for id in cfg.nodes() {
            let CfgNodeKind::Evaluate(expression) = cfg.node(*id).unwrap().kind else { continue };
            if let ExprKind::Call { .. } = lifted.hir.expression(expression).unwrap().kind {
                calls.push(*id);
            }
        }
        assert_eq!(calls.len(), 1);
        for budget in 0..256 {
            let facts = analyze(&lifted.hir, &cfg, &field, Some(budget)).unwrap();
            assert_ne!(
                facts.required_evaluation(calls[0]).certified(),
                Some(&true),
                "budget {budget}: {source}"
            );
        }
    }
}
