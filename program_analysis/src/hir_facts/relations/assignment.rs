//! Generated equation provenance at one source-owned constraint assignment.

use std::collections::BTreeSet;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use abstract_interpretation::solver::SolveResult;

use crate::hir_cfg::{Constraint, CfgNode, CfgNodeKind};
use crate::hir_facts::{
    AccessKey, AnalysisFacts, DescribeSignalAssignment, Fact, FactBlocker, FieldValue,
    NormalizedEquation, SourceSignalAssignment,
};
use crate::interprocedural::ValidatedComponentPorts;

/// One source-owned generated assignment with an exact checked storage target.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct GeneratedInputEquation {
    target: AccessKey,
    equation: NormalizedEquation,
}

impl GeneratedInputEquation {
    pub(crate) fn target(&self) -> &AccessKey {
        &self.target
    }

    pub(crate) fn equation(&self) -> &NormalizedEquation {
        &self.equation
    }
}

impl AnalysisFacts<'_> {
    pub(crate) fn generated_assignment_constant(
        &self,
        witness: NodeId,
    ) -> Fact<Option<FieldValue>> {
        let result = self.assignment_equation_result(witness, None).and_then(|assigned| {
            let solution = assigned
                .equation
                .singleton_solution(self.field)
                .map_err(|_| BTreeSet::from([FactBlocker::UnsupportedRelation(witness)]))?;
            Ok(solution.and_then(|(key, value)| (key == assigned.target).then_some(value)))
        });
        match result {
            Ok(value) => Fact::known(value),
            Err(blockers) => Fact::blocked(blockers),
        }
    }

    pub(crate) fn generated_assignment_equation(
        &self,
        witness: NodeId,
        ports: &ValidatedComponentPorts,
    ) -> Fact<GeneratedInputEquation> {
        match self.assignment_equation_result(witness, Some(ports)) {
            Ok(value) => Fact::known(value),
            Err(blockers) => Fact::blocked(blockers),
        }
    }

    fn assignment_equation_result(
        &self,
        witness: NodeId,
        ports: Option<&ValidatedComponentPorts>,
    ) -> Result<GeneratedInputEquation, BTreeSet<FactBlocker>> {
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
        let Some(SourceSignalAssignment::Generated { target: source, value: expression }) =
            effect.and_then(DescribeSignalAssignment::signal_assignment)
        else {
            return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        if source != target || expression != *value {
            return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        let constraint = self.paired_constraint(node)?;
        let blockers =
            self.relation_constraint_blockers_for(&constraint.kind, constraint.id, ports);
        if !blockers.is_empty() {
            return Err(blockers);
        }
        let key = match ports {
            Some(ports) => self.exact_closed_component_key(target, constraint.id, ports),
            None => self.exact_access_key_at(target, constraint.id),
        };
        let key = key.certified().ok_or_else(|| key.unavailable().cloned().unwrap_or_default())?;
        let equation = facts
            .get(&constraint.id)
            .and_then(|state| state.output.as_ref())
            .and_then(|state| state.must_equations().equation_at_origin(constraint.id))
            .ok_or_else(|| BTreeSet::from([FactBlocker::UnsupportedRelation(constraint.id)]))?;
        Ok(GeneratedInputEquation { target: key.clone(), equation: equation.clone() })
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
            let CfgNodeKind::Constraint(Constraint::Assignment { target, value: generated_value }) =
                &node.kind
            else {
                return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(node.id)]));
            };
            let CfgNodeKind::Witness { target: written, value } = &witness.kind else {
                return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
            };
            if target != written
                || generated_value != value
                || node.origin != witness.origin
                || found.replace(node).is_some()
            {
                return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
            }
        }
        found.ok_or_else(|| BTreeSet::from([FactBlocker::ForeignQuery]))
    }
}
