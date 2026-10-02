//! A resolved, finite generation path for the initial model-checking subset.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{FlowGraph, NodeId};
use parser::hir::{ExprId, SymbolKind};

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::forward::eval_expression_with_calls;
use crate::hir_facts::relations::complete::ProofBudget;
use crate::hir_facts::{AnalysisFacts, FactBlocker, FieldValue, VisitAccesses};

impl AnalysisFacts<'_> {
    pub(crate) fn unique_generation_path(
        &self,
        budget: &mut ProofBudget,
    ) -> Result<BTreeSet<NodeId>, BTreeSet<FactBlocker>> {
        let successors = self.model_successors(budget)?;
        let mut visited = BTreeSet::new();
        let mut current = self.cfg.entry();
        loop {
            if !visited.insert(current) {
                return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(current)]));
            }
            self.validate_model_control(current)?;
            if current == self.cfg.exit() {
                break;
            }
            let Some(next) = successors.get(&current) else {
                return Err(BTreeSet::from([FactBlocker::MissingExit]));
            };
            current = *next;
        }
        Ok(visited)
    }

    fn model_successors(
        &self,
        budget: &mut ProofBudget,
    ) -> Result<BTreeMap<NodeId, NodeId>, BTreeSet<FactBlocker>> {
        let mut successors = BTreeMap::new();
        for id in self.cfg.edges() {
            let Some(edge) = self.cfg.edge(*id) else {
                return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
            };
            if !budget.reserve_control_step() {
                return Err(BTreeSet::from([FactBlocker::Budget(edge.source)]));
            }
            let reachable = self.reachable_edge(*id);
            match reachable.certified() {
                Some(false) => {}
                Some(true) => {
                    if successors.insert(edge.source, edge.target).is_some() {
                        return Err(BTreeSet::from([FactBlocker::DeferredControl(edge.source)]));
                    }
                }
                None => {
                    return Err(reachable
                        .unavailable()
                        .cloned()
                        .unwrap_or_else(|| BTreeSet::from([FactBlocker::ForeignQuery])));
                }
            }
        }
        Ok(successors)
    }

    fn validate_model_control(&self, site: NodeId) -> Result<(), BTreeSet<FactBlocker>> {
        let Some(node) = self.cfg.node(site) else {
            return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        match &node.kind {
            CfgNodeKind::Branch { condition, .. } => {
                self.model_compile_time_value(site, *condition)?;
            }
            CfgNodeKind::Assert { condition } | CfgNodeKind::DeferredAssert { condition } => {
                let value = self.model_compile_time_value(site, *condition)?;
                if self.field.is_zero(&value) {
                    return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(site)]));
                }
            }
            CfgNodeKind::LoopHeader
            | CfgNodeKind::Instantiate { .. }
            | CfgNodeKind::DeferredAssignment { .. }
            | CfgNodeKind::OpaqueAssignment { .. }
            | CfgNodeKind::OpaqueEquality { .. }
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Opaque(_) => {
                return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(site)]));
            }
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::Evaluate(_)
            | CfgNodeKind::Witness { .. }
            | CfgNodeKind::Constraint { .. }
            | CfgNodeKind::Assignment { .. }
            | CfgNodeKind::Update { .. }
            | CfgNodeKind::Declaration { .. }
            | CfgNodeKind::Log => {}
        }
        Ok(())
    }

    fn model_compile_time_value(
        &self,
        site: NodeId,
        expression: ExprId,
    ) -> Result<FieldValue, BTreeSet<FactBlocker>> {
        let mut signal_independent = true;
        let complete = expression.visit_accesses_with(
            self.hir,
            &|call| self.exact_call_value(call).is_some(),
            &mut |path| {
                let Some(symbol) = self.hir.symbol(path.root) else {
                    signal_independent = false;
                    return;
                };
                match symbol.kind {
                    SymbolKind::Parameter | SymbolKind::Variable => {}
                    SymbolKind::Signal
                    | SymbolKind::Component
                    | SymbolKind::Bus
                    | SymbolKind::Tag => {
                        signal_independent = false;
                    }
                }
            },
        );
        if !complete || !signal_independent {
            return Err(BTreeSet::from([FactBlocker::OpaqueExpression(expression)]));
        }
        let value =
            self.site_state(site).and_then(|state| state.variables()).and_then(|variables| {
                eval_expression_with_calls(
                    self.hir,
                    self.field,
                    expression,
                    variables,
                    self.calls.as_deref(),
                )
            });
        value.ok_or_else(|| BTreeSet::from([FactBlocker::OpaqueExpression(expression)]))
    }
}
