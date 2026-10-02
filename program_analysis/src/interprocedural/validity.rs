//! Definite execution failures invalidate template certificates. Unknown
//! execution preserves the existing dependency-scoped availability checks.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use num_traits::Zero;
use parser::hir::{BusId, BusTarget, DefinitionRef, ExprId, ExprKind, SymbolId};
use parser::new_frontend::BinaryOperator;

use crate::hir_cfg::{build_cfg, CfgNodeKind};
use crate::hir_facts::{AnalysisFacts, Range};
use crate::interprocedural::ProjectSummaries;

impl ProjectSummaries<'_> {
    pub(super) fn template_definitely_fails(&self, facts: &AnalysisFacts<'_>) -> bool {
        let mut pending = Vec::new();
        if self.has_proven_failure(facts, &mut pending) {
            return true;
        }
        let mut visited = BTreeSet::new();
        while let Some(id) = pending.pop() {
            if !visited.insert(id) {
                continue;
            }
            let definition = DefinitionRef::Bus(id);
            let Ok(cfg) = build_cfg(self.hir(), definition) else { continue };
            let Ok(evidence) = self.symbolic_root(definition) else { continue };
            let Ok(facts) = self.analyze_for_evidence(&cfg, &evidence, None) else { continue };
            if self.has_proven_failure(&facts, &mut pending) {
                return true;
            }
        }
        false
    }

    fn has_proven_failure(&self, facts: &AnalysisFacts<'_>, buses: &mut Vec<BusId>) -> bool {
        for id in facts.cfg().nodes() {
            if facts.reachable_node(*id).certified() != Some(&true) {
                continue;
            }
            let Some(node) = facts.cfg().node(*id) else { continue };
            if self.node_definitely_fails(&node.kind, facts, buses) {
                return true;
            }
        }
        false
    }

    fn node_definitely_fails(
        &self,
        kind: &CfgNodeKind,
        facts: &AnalysisFacts<'_>,
        buses: &mut Vec<BusId>,
    ) -> bool {
        match kind {
            CfgNodeKind::Assert { condition } => self.proven_zero(*condition, facts),
            CfgNodeKind::Evaluate(expression) => {
                self.expression_definitely_fails(*expression, facts)
            }
            CfgNodeKind::Declaration { symbol } => {
                self.collect_bus(*symbol, buses);
                facts
                    .checked_symbol_dimensions(*symbol)
                    .is_err_and(|e| e.proves_invalid_execution())
            }
            CfgNodeKind::Assignment { target, .. }
            | CfgNodeKind::DeferredAssignment { target, .. }
            | CfgNodeKind::OpaqueAssignment { target, .. }
            | CfgNodeKind::Witness { target, .. }
            | CfgNodeKind::Instantiate { target, .. }
            | CfgNodeKind::Update { target, .. } => {
                facts.checked_access_bounds(target).is_err_and(|e| e.proves_invalid_execution())
            }
            CfgNodeKind::Constraint { target, .. } => target.as_ref().is_some_and(|target| {
                facts.checked_access_bounds(target).is_err_and(|e| e.proves_invalid_execution())
            }),
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::LoopHeader
            | CfgNodeKind::Branch { .. }
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Log
            | CfgNodeKind::Opaque(_)
            | CfgNodeKind::OpaqueEquality { .. } => false,
        }
    }

    fn expression_definitely_fails(&self, expression: ExprId, facts: &AnalysisFacts<'_>) -> bool {
        let Some(expression) = self.hir().expression(expression) else { return false };
        if let ExprKind::Access(path) = &expression.kind {
            return facts.checked_access_bounds(path).is_err_and(|e| e.proves_invalid_execution());
        }
        if let ExprKind::Binary {
            operator:
                BinaryOperator::Divide | BinaryOperator::IntegerDivide | BinaryOperator::Modulo,
            right,
            ..
        } = &expression.kind
        {
            return self.proven_zero(*right, facts);
        }
        false
    }

    fn proven_zero(&self, expression: ExprId, facts: &AnalysisFacts<'_>) -> bool {
        let value = facts.range(expression);
        let Some(Range::Exact(value)) = value.certified() else { return false };
        value.as_bigint().is_zero()
    }

    fn collect_bus(&self, symbol: SymbolId, buses: &mut Vec<BusId>) {
        let Some(symbol) = self.hir().symbol(symbol) else { return };
        let Some(BusTarget::Bus(id)) = &symbol.bus_type else { return };
        let Some(bus) = self.hir().bus(*id) else { return };
        if bus.parameters.is_empty() && symbol.bus_arguments.is_empty() {
            buses.push(*id);
        }
    }
}
