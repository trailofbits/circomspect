//! A resolved, finite generation path for the initial model-checking subset.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{FlowGraph, NodeId};
use abstract_interpretation::solver::SolveResult;
use parser::hir::{ExprId, SymbolKind};
use parser::hir::ControlGuard;

use crate::hir_cfg::{CfgEdge, CfgNodeKind, EdgeKind};
use crate::hir_facts::forward::eval_expression_with_calls;
use crate::hir_facts::relations::complete::ProofBudget;
use crate::hir_facts::{AnalysisFacts, FactBlocker, FieldValue, VisitAccesses};
use crate::interprocedural::ValidatedConstructorReads;

#[derive(Clone, Copy)]
enum GenerationScope<'a> {
    Leaf,
    CompletedChildren(&'a ValidatedConstructorReads),
}

impl AnalysisFacts<'_> {
    pub(crate) fn unique_generation_path(
        &self,
        budget: &mut ProofBudget,
    ) -> Result<BTreeSet<NodeId>, BTreeSet<FactBlocker>> {
        self.generation_path(budget, GenerationScope::Leaf)
    }

    pub(crate) fn unique_generation_path_with(
        &self,
        budget: &mut ProofBudget,
        constructors: &ValidatedConstructorReads,
    ) -> Result<BTreeSet<NodeId>, BTreeSet<FactBlocker>> {
        if self.evidence_binding.as_ref() != Some(constructors.evidence()) {
            return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        self.generation_path(budget, GenerationScope::CompletedChildren(constructors))
    }

    fn generation_path(
        &self,
        budget: &mut ProofBudget,
        scope: GenerationScope<'_>,
    ) -> Result<BTreeSet<NodeId>, BTreeSet<FactBlocker>> {
        if let Some(path) = self.linear_generation_path(budget, scope)? {
            return Ok(path);
        }
        let successors = self.model_successors(budget)?;
        let mut visited = BTreeSet::new();
        let mut current = self.cfg.entry();
        loop {
            if !visited.insert(current) {
                return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(current)]));
            }
            self.validate_model_control(current, scope)?;
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

    fn linear_generation_path(
        &self,
        budget: &mut ProofBudget,
        scope: GenerationScope<'_>,
    ) -> Result<Option<BTreeSet<NodeId>>, BTreeSet<FactBlocker>> {
        let Some(successors) = self.linear_successors() else { return Ok(None) };
        let Some(visited) = self.complete_linear_path(&successors) else { return Ok(None) };
        self.validate_linear_path(&visited, &successors, budget, scope)?;
        Ok(Some(visited))
    }

    fn linear_successors(&self) -> Option<BTreeMap<NodeId, (NodeId, EdgeKind)>> {
        let SolveResult::Complete(_) = &self.forward else { return None };
        if self.cfg.edges().len().checked_add(1) != Some(self.cfg.nodes().len()) {
            return None;
        }
        let mut successors = BTreeMap::new();
        for id in self.cfg.edges() {
            let edge = self.cfg.edge(*id)?;
            let node = self.cfg.node(edge.source)?;
            if !linear_edge_supported(&node.kind, edge.payload)
                || successors.insert(edge.source, (edge.target, edge.payload.kind)).is_some()
            {
                return None;
            }
        }
        Some(successors)
    }

    fn complete_linear_path(
        &self,
        successors: &BTreeMap<NodeId, (NodeId, EdgeKind)>,
    ) -> Option<BTreeSet<NodeId>> {
        let mut visited = BTreeSet::new();
        let mut current = self.cfg.entry();
        while visited.insert(current) && current != self.cfg.exit() {
            let (next, _) = successors.get(&current)?;
            current = *next;
        }
        if current != self.cfg.exit() || visited.len() != self.cfg.nodes().len() {
            return None;
        }
        Some(visited)
    }

    fn validate_linear_path(
        &self,
        visited: &BTreeSet<NodeId>,
        successors: &BTreeMap<NodeId, (NodeId, EdgeKind)>,
        budget: &mut ProofBudget,
        scope: GenerationScope<'_>,
    ) -> Result<(), BTreeSet<FactBlocker>> {
        for site in visited {
            if *site != self.cfg.exit() && !budget.reserve_control_step() {
                return Err(BTreeSet::from([FactBlocker::Budget(*site)]));
            }
            let Some(node) = self.cfg.node(*site) else {
                return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
            };
            if let CfgNodeKind::Branch { condition, .. } = &node.kind {
                let Some((_, kind)) = successors.get(site) else {
                    return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
                };
                let value = self.model_compile_time_value(*site, *condition)?;
                let selected = match kind {
                    EdgeKind::True => !self.field.is_zero(&value),
                    EdgeKind::False => self.field.is_zero(&value),
                    EdgeKind::Normal | EdgeKind::Loop | EdgeKind::Return => false,
                };
                if !selected {
                    return Err(BTreeSet::from([FactBlocker::DeferredControl(*site)]));
                }
            } else {
                self.validate_model_control(*site, scope)?;
            }
        }
        Ok(())
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
            match reachable.into_result() {
                Ok(false) => {}
                Ok(true) => {
                    if successors.insert(edge.source, edge.target).is_some() {
                        return Err(BTreeSet::from([FactBlocker::DeferredControl(edge.source)]));
                    }
                }
                Err(blockers) => return Err(blockers),
            }
        }
        Ok(successors)
    }

    fn validate_model_control(
        &self,
        site: NodeId,
        scope: GenerationScope<'_>,
    ) -> Result<(), BTreeSet<FactBlocker>> {
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
            CfgNodeKind::Instantiate { value, .. } => match scope {
                GenerationScope::CompletedChildren(constructors)
                    if constructors.contains(*value) => {}
                GenerationScope::Leaf | GenerationScope::CompletedChildren(_) => {
                    return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(site)]));
                }
            },
            CfgNodeKind::LoopHeader
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
            | CfgNodeKind::Constraint(_)
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

fn linear_edge_supported(node: &CfgNodeKind, edge: &CfgEdge) -> bool {
    match (node, edge.kind) {
        (
            CfgNodeKind::Branch { condition, guard: ControlGuard::CheckedCompileTime },
            EdgeKind::True | EdgeKind::False,
        ) => {
            edge.condition == Some(*condition)
                && edge.guard == Some(ControlGuard::CheckedCompileTime)
        }
        (_, EdgeKind::Normal) => match node {
            CfgNodeKind::Branch { .. } => false,
            _ => edge.condition.is_none() && edge.guard.is_none(),
        },
        (_, EdgeKind::True | EdgeKind::False | EdgeKind::Loop | EdgeKind::Return) => false,
    }
}
