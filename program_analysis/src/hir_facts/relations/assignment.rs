//! Generated constant provenance at one source-owned constraint assignment.

use std::collections::BTreeSet;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use abstract_interpretation::solver::SolveResult;
use parser::hir::Effect;

use crate::hir_cfg::{CfgNode, CfgNodeKind};
use crate::hir_facts::{AnalysisFacts, Fact, FactBlocker, FieldValue};

impl AnalysisFacts<'_> {
    pub(crate) fn generated_assignment_constant(
        &self,
        witness: NodeId,
    ) -> Fact<Option<FieldValue>> {
        match self.assignment_constant_result(witness) {
            Ok(value) => Fact::known(value),
            Err(blockers) => Fact::blocked(blockers),
        }
    }

    fn assignment_constant_result(
        &self,
        witness: NodeId,
    ) -> Result<Option<FieldValue>, BTreeSet<FactBlocker>> {
        let SolveResult::Complete(facts) = &self.forward else {
            return Err(self.forward_completion_blockers());
        };
        let node =
            self.cfg.node(witness).ok_or_else(|| BTreeSet::from([FactBlocker::ForeignQuery]))?;
        let CfgNodeKind::Witness { target, value } = &node.kind else {
            return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        let origin = node.origin.ok_or_else(|| BTreeSet::from([FactBlocker::ForeignQuery]))?;
        let effect =
            self.hir.block(origin.block).and_then(|block| block.effects.get(origin.effect_index));
        let Some(Effect::ConstraintAssignment { target: source, value: expression, .. }) = effect
        else {
            return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        if source != target || expression != value {
            return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        let constraint = self.paired_constraint(node)?;
        let blockers = self.relation_constraint_blockers(&constraint.kind, constraint.id);
        if !blockers.is_empty() {
            return Err(blockers);
        }
        let key = self.exact_access_key_at(target, constraint.id);
        let key = key.certified().ok_or_else(|| key.unavailable().cloned().unwrap_or_default())?;
        let equation = facts
            .get(&constraint.id)
            .and_then(|state| state.output.as_ref())
            .and_then(|state| state.must_equations().equation_at_origin(constraint.id))
            .ok_or_else(|| BTreeSet::from([FactBlocker::UnsupportedRelation(constraint.id)]))?;
        let solution = equation
            .singleton_solution(self.field)
            .map_err(|_| BTreeSet::from([FactBlocker::UnsupportedRelation(constraint.id)]))?;
        Ok(solution.and_then(|(assigned, value)| (assigned == *key).then_some(value)))
    }

    fn paired_constraint(&self, witness: &CfgNode) -> Result<&CfgNode, BTreeSet<FactBlocker>> {
        let mut found = None;
        for edge in self.cfg.edges() {
            let edge =
                self.cfg.edge(*edge).ok_or_else(|| BTreeSet::from([FactBlocker::ForeignQuery]))?;
            if edge.source != witness.id {
                continue;
            }
            let node = self
                .cfg
                .node(edge.target)
                .ok_or_else(|| BTreeSet::from([FactBlocker::ForeignQuery]))?;
            let CfgNodeKind::Constraint { target: Some(target), left, right: None } = &node.kind
            else {
                return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(node.id)]));
            };
            let CfgNodeKind::Witness { target: written, value } = &witness.kind else {
                return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
            };
            if target != written
                || left != value
                || node.origin != witness.origin
                || found.replace(node).is_some()
            {
                return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
            }
        }
        found.ok_or_else(|| BTreeSet::from([FactBlocker::ForeignQuery]))
    }
}
