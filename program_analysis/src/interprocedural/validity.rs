//! Definite execution failures invalidate template certificates. Unknown
//! execution preserves the existing dependency-scoped availability checks.

use std::collections::BTreeSet;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use num_traits::Zero;
use parser::hir::{BusId, BusTarget, CallTarget, DefinitionRef, ExprId, ExprKind, SymbolId};
use parser::new_frontend::BinaryOperator;

use crate::hir_cfg::{Constraint, build_cfg, CfgNodeKind};
use crate::hir_facts::{AnalysisFacts, Range};
use crate::interprocedural::{
    CallContext, CallOwner, CallProvenance, CallSite, ProjectSummaries, SummaryBlocker,
};

impl ProjectSummaries<'_> {
    pub(super) fn template_definitely_fails(
        &self,
        facts: &AnalysisFacts<'_>,
    ) -> Result<bool, SummaryBlocker> {
        let mut pending = Vec::new();
        if self.has_proven_failure(facts, &mut pending) || self.required_functions_fail(facts)? {
            return Ok(true);
        }
        let mut visited = BTreeSet::new();
        while let Some(id) = pending.pop() {
            if !visited.insert(id) {
                continue;
            }
            if self.bus_definitely_fails(id, &mut pending)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn bus_definitely_fails(
        &self,
        id: BusId,
        pending: &mut Vec<BusId>,
    ) -> Result<bool, SummaryBlocker> {
        let definition = DefinitionRef::Bus(id);
        let Ok(cfg) = build_cfg(self.hir(), definition) else { return Ok(false) };
        let Ok(evidence) = self.symbolic_root(definition) else { return Ok(false) };
        let Ok(facts) = self.analyze_for_evidence(&cfg, &evidence, None) else { return Ok(false) };
        Ok(self.has_proven_failure(&facts, pending) || self.required_functions_fail(&facts)?)
    }

    fn has_proven_failure(&self, facts: &AnalysisFacts<'_>, buses: &mut Vec<BusId>) -> bool {
        if facts.definitely_repeats_any_body_write().certified() == Some(&true) {
            return true;
        }
        for id in facts.cfg().nodes() {
            if facts.reachable_node(*id).certified() != Some(&true) {
                continue;
            }
            let Some(node) = facts.cfg().node(*id) else { continue };
            if let CfgNodeKind::Declaration { symbol } = &node.kind {
                self.collect_bus(*symbol, buses);
            }
            if self.node_definitely_fails(&node.kind, facts) {
                return true;
            }
        }
        false
    }

    fn node_definitely_fails(&self, kind: &CfgNodeKind, facts: &AnalysisFacts<'_>) -> bool {
        match kind {
            CfgNodeKind::Assert { condition } | CfgNodeKind::DeferredAssert { condition } => {
                Self::proven_zero(*condition, facts)
            }
            CfgNodeKind::Evaluate(expression) => {
                self.expression_definitely_fails(*expression, facts)
            }
            CfgNodeKind::Declaration { symbol } => facts
                .checked_symbol_dimensions(*symbol)
                .is_err_and(crate::hir_facts::AccessHandleError::proves_invalid_execution),
            CfgNodeKind::Assignment { target, .. }
            | CfgNodeKind::DeferredAssignment { target, .. }
            | CfgNodeKind::OpaqueAssignment { target, .. }
            | CfgNodeKind::Witness { target, .. }
            | CfgNodeKind::Instantiate { target, .. }
            | CfgNodeKind::Update { target, .. }
            | CfgNodeKind::Constraint(Constraint::Assignment { target, .. }) => facts
                .checked_access_bounds(target)
                .is_err_and(crate::hir_facts::AccessHandleError::proves_invalid_execution),
            CfgNodeKind::Constraint(Constraint::Equality { .. })
            | CfgNodeKind::Entry
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
            return facts
                .checked_access_bounds(path)
                .is_err_and(crate::hir_facts::AccessHandleError::proves_invalid_execution);
        }
        if let ExprKind::Binary {
            operator:
                BinaryOperator::Divide | BinaryOperator::IntegerDivide | BinaryOperator::Modulo,
            right,
            ..
        } = &expression.kind
        {
            return Self::proven_zero(*right, facts);
        }
        false
    }

    fn required_functions_fail(&self, facts: &AnalysisFacts<'_>) -> Result<bool, SummaryBlocker> {
        const MAX_CONTEXTS: usize = 64;
        let mut pending = Vec::new();
        self.collect_required_functions(facts, &mut pending);
        let mut visited = BTreeSet::new();
        while let Some(context) = pending.pop() {
            if !visited.insert(context.clone()) {
                continue;
            }
            if visited.len() > MAX_CONTEXTS {
                return Err(SummaryBlocker::ContextBudget);
            }
            let DefinitionRef::Function(id) = context.definition() else { continue };
            let failure = self.with_local_function(id, &context, |_, _, facts| {
                self.collect_required_functions(facts, &mut pending);
                Ok(self.required_local_failure(facts))
            });
            // Unavailable function facts cannot prove failure or invalidate independent facts.
            if failure == Ok(true) {
                return Ok(true);
            }
            if let Err(SummaryBlocker::InvalidAssignment(_) | SummaryBlocker::InvalidValueUse(_)) =
                failure
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn required_local_failure(&self, facts: &AnalysisFacts<'_>) -> bool {
        for id in facts.cfg().nodes() {
            if !required_node(facts, *id) {
                continue;
            }
            let Some(node) = facts.cfg().node(*id) else { continue };
            if self.node_definitely_fails(&node.kind, facts) {
                return true;
            }
        }
        false
    }

    fn collect_required_functions(
        &self,
        facts: &AnalysisFacts<'_>,
        pending: &mut Vec<CallContext>,
    ) {
        let owner = CallOwner::Definition(facts.definition());
        for site in self.graph().calls_from(owner) {
            if let Some(context) = self.required_function_context(site, facts) {
                pending.push(context);
            }
        }
    }

    fn required_function_context(
        &self,
        site: &CallSite,
        facts: &AnalysisFacts<'_>,
    ) -> Option<CallContext> {
        if site.provenance == CallProvenance::Unattached {
            return None;
        }
        let expression = site.expression?;
        let required = facts.cfg().nodes().iter().any(|id| {
            let Some(CfgNodeKind::Evaluate(evaluated)) =
                facts.cfg().node(*id).map(|node| &node.kind)
            else {
                return false;
            };
            *evaluated == expression && required_node(facts, *id)
        });
        if !required {
            return None;
        }
        self.evaluated_function_context(site, expression, facts)
    }

    fn evaluated_function_context(
        &self,
        site: &CallSite,
        expression: ExprId,
        facts: &AnalysisFacts<'_>,
    ) -> Option<CallContext> {
        let Some(ExprKind::Call { target: CallTarget::Function(function), arguments }) =
            self.hir().expression(expression).map(|expression| &expression.kind)
        else {
            return None;
        };
        let definition = DefinitionRef::Function(*function);
        if site.resolved() != Some(definition) {
            return None;
        }
        // A call is evaluated before its still-untyped assignment consumes the return value.
        // This proves only required evaluation, not a valid assignment or usable call result.
        let arguments = self.exact_call_arguments(arguments, facts).ok()?;
        self.context_for(definition, arguments).ok()
    }

    fn proven_zero(expression: ExprId, facts: &AnalysisFacts<'_>) -> bool {
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

fn required_node(facts: &AnalysisFacts<'_>, node: NodeId) -> bool {
    facts.required_evaluation(node).certified() == Some(&true)
}
