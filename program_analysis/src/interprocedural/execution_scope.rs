//! Execution checks distinguish proven failure from supported complete execution.

use std::collections::BTreeSet;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use num_traits::Zero;
use parser::hir::{
    BusId, BusTarget, CallTarget, ControlGuard, DefinitionRef, ExprId, ExprKind, FunctionId,
    Symbol, SymbolId, SymbolKind,
};
use parser::frontend::{AssignmentOperator, BinaryOperator};

use crate::hir_cfg::{build_cfg, Constraint, CfgNodeKind, DefinitionCfg};
use crate::hir_facts::{AnalysisFacts, FieldContext, Range};
use crate::interprocedural::{
    CallContext, CallOwner, CallProvenance, CallSite, ContextEvidence, ProjectAnalysis,
    SummaryBlocker,
};
use crate::interprocedural::summary::certified;

impl ProjectAnalysis<'_> {
    /// Reject a bound definition scope with invalid source or a known failure path.
    ///
    /// Unknown-type regions may remain. Passing this check does not prove
    /// successful completion; rules must certify their own value, reachability,
    /// and dependency predicates. Complete-scope consumers additionally call
    /// `validated_definition`.
    ///
    /// # Errors
    /// Returns the source, provenance, or execution blocker for this scope.
    pub fn check_warning_execution_scope(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.check_call_execution_scope(facts, evidence)?;
        if self.sources().definition_has_hard_source_issue(facts.definition())? {
            return Err(SummaryBlocker::IncompleteDefinition);
        }
        Ok(())
    }

    /// Reject known caller failures without discarding independent facts in partial source.
    pub(super) fn check_call_execution_scope(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.check_facts_for_evidence(facts, evidence)?;
        self.sources().validated_header(facts.definition())?;
        match facts.definition() {
            DefinitionRef::Function(_) => {}
            DefinitionRef::Template(id) => {
                let template = self.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
                if template.custom || template.external {
                    return Err(SummaryBlocker::ExternalSummary);
                }
            }
            DefinitionRef::Bus(_) => return Err(SummaryBlocker::UnsupportedContext),
        }
        if self.definition_definitely_fails(facts)? {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        Ok(())
    }
}

// Proven failures invalidate independent certificates; uncertainty alone does not.
impl ProjectAnalysis<'_> {
    pub(super) fn definition_definitely_fails(
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

// Complete return evidence requires every reachable function operation to be supported.
impl ProjectAnalysis<'_> {
    pub(super) fn may_fail_before_return(
        &self,
        id: FunctionId,
        cfg: &DefinitionCfg,
        facts: &AnalysisFacts<'_>,
    ) -> bool {
        let owner = CallOwner::Definition(DefinitionRef::Function(id));
        for site in self.graph().calls_from(owner) {
            if let Some(DefinitionRef::Function(_)) = site.resolved() {
                continue;
            }
            let Some(expression) = site.expression else { return true };
            if facts.reachable_expression(expression).certified() != Some(&false) {
                return true;
            }
        }
        let field = FieldContext::for_curve(self.curve().clone());
        for id in cfg.nodes() {
            let Some(node) = cfg.node(*id) else { return true };
            match facts.reachable_node(*id).certified() {
                Some(false) => continue,
                None => return true,
                Some(true) => {}
            }
            if self.function_node_may_fail(*id, &node.kind, facts, &field) {
                return true;
            }
        }
        false
    }

    fn function_node_may_fail(
        &self,
        id: NodeId,
        kind: &CfgNodeKind,
        facts: &AnalysisFacts<'_>,
        field: &FieldContext,
    ) -> bool {
        match kind {
            CfgNodeKind::Assert { condition } | CfgNodeKind::DeferredAssert { condition } => {
                !is_proven_nonzero(facts.range(*condition).certified(), field)
            }
            CfgNodeKind::Opaque(_)
            | CfgNodeKind::OpaqueAssignment { .. }
            | CfgNodeKind::OpaqueEquality { .. }
            | CfgNodeKind::Instantiate { .. }
            | CfgNodeKind::Witness { .. }
            | CfgNodeKind::Constraint(_) => true,
            CfgNodeKind::Assignment { target, operator, .. } => {
                *operator != AssignmentOperator::Assign
                    || facts.checked_access_bounds(target).is_err()
            }
            CfgNodeKind::DeferredAssignment { target, operator, .. } => {
                *operator != AssignmentOperator::Assign
                    || !facts.resolved_deferred_assignment(id)
                    || facts.checked_access_bounds(target).is_err()
            }
            CfgNodeKind::Update { target, .. } => facts.checked_access_bounds(target).is_err(),
            CfgNodeKind::Evaluate(expression) => {
                self.expression_may_fail(*expression, facts, field)
            }
            CfgNodeKind::Declaration { symbol } => self.declaration_may_fail(*symbol, facts),
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::LoopHeader
            | CfgNodeKind::Branch { .. }
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Log => false,
        }
    }

    pub(super) fn expression_may_fail(
        &self,
        id: ExprId,
        facts: &AnalysisFacts<'_>,
        field: &FieldContext,
    ) -> bool {
        let Some(expression) = self.hir().expression(id) else { return true };
        match &expression.kind {
            ExprKind::Call { target: CallTarget::Function(_), .. }
            | ExprKind::Number(_)
            | ExprKind::Array(_)
            | ExprKind::Tuple(_)
            | ExprKind::Unary { .. }
            | ExprKind::Ternary { .. }
            | ExprKind::Parallel(_) => false,
            ExprKind::Opaque(_) | ExprKind::AnonymousComponent { .. } | ExprKind::Call { .. } => {
                true
            }
            ExprKind::Access(path) => facts.checked_access_bounds(path).is_err(),
            ExprKind::Binary { operator, right, .. } => match operator {
                BinaryOperator::Divide | BinaryOperator::IntegerDivide | BinaryOperator::Modulo => {
                    !is_proven_nonzero(facts.range(*right).certified(), field)
                }
                BinaryOperator::Power | BinaryOperator::ShiftLeft | BinaryOperator::ShiftRight => {
                    true
                }
                BinaryOperator::BooleanOr
                | BinaryOperator::BooleanAnd
                | BinaryOperator::Equal
                | BinaryOperator::NotEqual
                | BinaryOperator::Less
                | BinaryOperator::Greater
                | BinaryOperator::LessEqual
                | BinaryOperator::GreaterEqual
                | BinaryOperator::BitOr
                | BinaryOperator::BitXor
                | BinaryOperator::BitAnd
                | BinaryOperator::Add
                | BinaryOperator::Subtract
                | BinaryOperator::Multiply => false,
            },
        }
    }
}

// Negative project-use claims require supported complete template execution.
impl ProjectAnalysis<'_> {
    pub(super) fn check_complete_template_execution(
        &self,
        cfg: &DefinitionCfg,
        facts: &AnalysisFacts<'_>,
    ) -> Result<(), SummaryBlocker> {
        let field = FieldContext::for_curve(self.curve().clone());
        for id in cfg.nodes() {
            let node = cfg.node(*id).ok_or(SummaryBlocker::ExternalSummary)?;
            if !*certified(&facts.reachable_node(*id))? {
                continue;
            }
            if self.template_node_may_fail(*id, &node.kind, facts, &field) {
                return Err(SummaryBlocker::UnsupportedContext);
            }
        }
        Ok(())
    }

    fn template_node_may_fail(
        &self,
        id: NodeId,
        kind: &CfgNodeKind,
        facts: &AnalysisFacts<'_>,
        field: &FieldContext,
    ) -> bool {
        match kind {
            CfgNodeKind::Assert { condition } | CfgNodeKind::DeferredAssert { condition } => {
                !is_proven_nonzero(facts.range(*condition).certified(), field)
            }
            CfgNodeKind::Evaluate(expression) => {
                self.template_expression_may_fail(*expression, facts.cfg(), facts, field)
            }
            CfgNodeKind::Witness { target, .. }
            | CfgNodeKind::Instantiate { target, .. }
            | CfgNodeKind::Update { target, .. } => facts.checked_access_bounds(target).is_err(),
            CfgNodeKind::Constraint(Constraint::Assignment { target, .. }) => {
                facts.checked_access_bounds(target).is_err()
            }
            CfgNodeKind::Assignment { target, operator, .. } => {
                *operator != AssignmentOperator::Assign
                    || facts.checked_access_bounds(target).is_err()
            }
            CfgNodeKind::DeferredAssignment { target, operator, .. } => {
                *operator != AssignmentOperator::Assign
                    || !facts.resolved_deferred_assignment(id)
                    || facts.checked_access_bounds(target).is_err()
            }
            CfgNodeKind::Branch { condition, guard } => match guard {
                ControlGuard::CheckedCompileTime => {
                    let range = facts.range(*condition);
                    let Some(Range::Exact(_)) = range.certified() else { return true };
                    false
                }
                ControlGuard::DeferredScalar | ControlGuard::WitnessOnly => true,
            },
            CfgNodeKind::Opaque(_)
            | CfgNodeKind::OpaqueAssignment { .. }
            | CfgNodeKind::OpaqueEquality { .. }
            | CfgNodeKind::LoopHeader => true,
            CfgNodeKind::Declaration { symbol } => self.declaration_may_fail(*symbol, facts),
            CfgNodeKind::Constraint(Constraint::Equality { .. })
            | CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Log => false,
        }
    }

    pub(super) fn declaration_may_fail(&self, id: SymbolId, facts: &AnalysisFacts<'_>) -> bool {
        let Some(symbol) = self.hir().symbol(id) else { return true };
        if facts.checked_symbol_dimensions(id).is_err() {
            return true;
        }
        if let SymbolKind::Bus = symbol.kind {
            return self.bus_schema_may_fail(symbol);
        }
        false
    }

    fn bus_schema_may_fail(&self, symbol: &Symbol) -> bool {
        let Some(BusTarget::Bus(id)) = &symbol.bus_type else { return true };
        let Some(bus) = self.hir().bus(*id) else { return true };
        if !bus.parameters.is_empty() || !symbol.bus_arguments.is_empty() {
            return true;
        }
        let definition = DefinitionRef::Bus(*id);
        let Ok(cfg) = build_cfg(self.hir(), definition) else { return true };
        let Ok(evidence) = self.symbolic_root(definition) else { return true };
        let Ok(facts) = self.analyze_for_evidence(&cfg, &evidence, None) else { return true };
        let field = FieldContext::for_curve(self.curve().clone());
        for id in cfg.nodes() {
            let Some(node) = cfg.node(*id) else { return true };
            if facts.reachable_node(*id).certified() != Some(&true) {
                return true;
            }
            match node.kind {
                CfgNodeKind::Entry | CfgNodeKind::Exit => {}
                CfgNodeKind::Evaluate(expression) => {
                    if self.expression_may_fail(expression, &facts, &field) {
                        return true;
                    }
                }
                CfgNodeKind::Declaration { symbol } => {
                    let Some(field) = self.hir().symbol(symbol) else { return true };
                    if field.kind == SymbolKind::Bus
                        || facts.checked_symbol_dimensions(symbol).is_err()
                    {
                        return true;
                    }
                }
                CfgNodeKind::LoopHeader
                | CfgNodeKind::Branch { .. }
                | CfgNodeKind::Assignment { .. }
                | CfgNodeKind::DeferredAssignment { .. }
                | CfgNodeKind::Update { .. }
                | CfgNodeKind::Instantiate { .. }
                | CfgNodeKind::Witness { .. }
                | CfgNodeKind::Constraint(_)
                | CfgNodeKind::Return(_)
                | CfgNodeKind::Assert { .. }
                | CfgNodeKind::DeferredAssert { .. }
                | CfgNodeKind::Log
                | CfgNodeKind::Opaque(_)
                | CfgNodeKind::OpaqueAssignment { .. }
                | CfgNodeKind::OpaqueEquality { .. } => return true,
            }
        }
        false
    }

    fn template_expression_may_fail(
        &self,
        id: ExprId,
        cfg: &DefinitionCfg,
        facts: &AnalysisFacts<'_>,
        field: &FieldContext,
    ) -> bool {
        let Some(expression) = self.hir().expression(id) else { return true };
        if let ExprKind::Call { target: CallTarget::Template(_), .. } = &expression.kind {
            return !cfg.nodes().iter().any(|node| {
                if let Some(CfgNodeKind::Instantiate { value, .. }) =
                    cfg.node(*node).map(|node| &node.kind)
                {
                    *value == id
                } else {
                    false
                }
            });
        }
        if let ExprKind::Call { .. } = &expression.kind {
            return true;
        }
        self.expression_may_fail(id, facts, field)
    }
}

pub(super) fn is_proven_nonzero(value: Option<&Range>, field: &FieldContext) -> bool {
    match value {
        Some(Range::Exact(value)) => !field.is_zero(value),
        Some(Range::Canonical | Range::Unreachable) | None => false,
    }
}
