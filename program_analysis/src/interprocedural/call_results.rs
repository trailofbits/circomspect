//! Complete exact call results permitted to specialize one definition's local transfer.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use parser::hir::{CallTarget, DefinitionRef, ExprId, ExprKind, FunctionId};

use crate::scalar_evidence::ScalarExpressionEvidence;
use crate::hir_cfg::{build_cfg_with_exact_calls, CfgNodeKind, DefinitionCfg};
use crate::hir_facts::{AnalysisFacts, FieldValue, OwnedAnalysisOptions, Range};
use crate::hir_facts::analyze_owned_with_scalar_calls;
use crate::interprocedural::{CallContext, CallOwner, CallProvenance, CallSite, ProjectSummaries};
use crate::interprocedural::SummaryBlocker;
use parser::hir::SymbolId;
use std::collections::BTreeMap;

enum Visit {
    Enter(FunctionId),
    Leave(FunctionId),
}

impl ProjectSummaries<'_> {
    pub(super) fn with_refined_facts<T>(
        &self,
        definition: DefinitionRef,
        parameters: BTreeMap<SymbolId, FieldValue>,
        work: impl FnOnce(&DefinitionCfg, &AnalysisFacts<'_>) -> Result<T, SummaryBlocker>,
    ) -> Result<T, SummaryBlocker> {
        let facts = self.refined_facts(definition, parameters, None)?;
        work(facts.cfg(), &facts)
    }

    pub(super) fn refined_facts<'a>(
        &'a self,
        definition: DefinitionRef,
        parameters: BTreeMap<SymbolId, FieldValue>,
        budget: Option<usize>,
    ) -> Result<AnalysisFacts<'a>, SummaryBlocker> {
        const MAX_REFINEMENTS: usize = 64;
        let mut calls =
            ScalarExpressionEvidence::empty(self.hir(), definition, self.curve().clone());
        for _ in 0..MAX_REFINEMENTS {
            let cfg = build_cfg_with_exact_calls(self.hir(), definition, &calls)
                .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
            let facts = analyze_owned_with_scalar_calls(
                self.hir(),
                cfg,
                self.field_context(),
                OwnedAnalysisOptions { values: parameters.clone(), calls: calls.clone(), budget },
            )
            .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
            let discovered = self.certified_scalar_evidence(definition, &facts);
            let mut next = calls.clone();
            let changed =
                next.merge(&discovered).map_err(|()| SummaryBlocker::UnsupportedContext)?;
            if !changed {
                self.check_exact_assignment_shapes(facts.cfg(), &facts)?;
                return Ok(facts);
            }
            calls = next;
        }
        Err(SummaryBlocker::ContextBudget)
    }

    fn check_exact_assignment_shapes(
        &self,
        cfg: &DefinitionCfg,
        facts: &AnalysisFacts<'_>,
    ) -> Result<(), SummaryBlocker> {
        for id in cfg.nodes() {
            let Some(CfgNodeKind::OpaqueAssignment { target, value, .. }) =
                cfg.node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            if facts.exact_call_value(*value).is_none() || !target.steps.is_empty() {
                continue;
            }
            let Some(symbol) = self.hir().symbol(target.terminal) else { continue };
            if symbol.rank == 0 && symbol.bus_type.is_none() {
                continue;
            }
            match facts.reachable_node(*id).certified() {
                Some(false) => {}
                Some(true) => return Err(SummaryBlocker::InvalidAssignment(*value)),
                None => return Err(SummaryBlocker::UnsupportedContext),
            }
        }
        Ok(())
    }

    pub(super) fn exact_site_context(
        &self,
        site: &CallSite,
        facts: &AnalysisFacts<'_>,
    ) -> Result<CallContext, SummaryBlocker> {
        if site.provenance != CallProvenance::Provisional
            || site.owner != CallOwner::Definition(facts.definition())
            || self.hir().identity() != facts.hir().identity()
            || self.curve() != facts.curve()
        {
            return Err(SummaryBlocker::ForeignCall);
        }
        let expression = site.expression.ok_or(SummaryBlocker::UnsupportedCallForm)?;
        if facts.exact_call_value(expression).is_none()
            || facts.reachable_expression(expression).certified() != Some(&true)
        {
            return Err(SummaryBlocker::ExternalSummary);
        }
        let Some(ExprKind::Call { target: CallTarget::Function(id), arguments }) =
            self.hir().expression(expression).map(|expr| &expr.kind)
        else {
            return Err(SummaryBlocker::UnsupportedCallForm);
        };
        if site.resolved() != Some(DefinitionRef::Function(*id)) {
            return Err(SummaryBlocker::ForeignCall);
        }
        let arguments = self.exact_call_arguments(arguments, facts)?;
        self.context_for(DefinitionRef::Function(*id), arguments)
    }

    fn certified_scalar_evidence(
        &self,
        definition: DefinitionRef,
        facts: &AnalysisFacts<'_>,
    ) -> ScalarExpressionEvidence {
        let mut results =
            ScalarExpressionEvidence::empty(self.hir(), definition, self.curve().clone());
        if facts.definition() != definition
            || self.hir().identity() != facts.hir().identity()
            || self.curve() != facts.curve()
        {
            return results;
        }
        let owner = CallOwner::Definition(definition);
        for site in self.graph().calls_from(owner) {
            let Some((expression, callee, arguments)) = self.checked_call_site(site, facts) else {
                continue;
            };
            let Some((value, dependencies)) = self.complete_exact_value(callee, arguments, facts)
            else {
                continue;
            };
            results.insert_call(expression, value, dependencies);
        }
        for expression in self.hir().expressions() {
            let ExprKind::Access(path) = &expression.kind else { continue };
            if !path.steps.is_empty() {
                continue;
            }
            let fact = facts.range(expression.id);
            let Some(Range::Exact(value)) = fact.certified() else { continue };
            results.insert_access(expression.id, value.clone());
        }
        results
    }

    fn checked_call_site<'a>(
        &'a self,
        site: &CallSite,
        facts: &AnalysisFacts<'_>,
    ) -> Option<(ExprId, FunctionId, &'a [ExprId])> {
        if site.provenance == CallProvenance::Unattached {
            return None;
        }
        let DefinitionRef::Function(callee) = site.resolved()? else { return None };
        if !self.acyclic_function_calls(callee) {
            return None;
        }
        let expression = site.expression?;
        if facts.reachable_expression(expression).certified() != Some(&true) {
            return None;
        }
        let ExprKind::Call { target: CallTarget::Function(id), arguments } =
            &self.hir().expression(expression)?.kind
        else {
            return None;
        };
        (*id == callee).then_some((expression, callee, arguments.as_slice()))
    }

    fn complete_exact_value(
        &self,
        callee: FunctionId,
        arguments: &[ExprId],
        facts: &AnalysisFacts<'_>,
    ) -> Option<(FieldValue, BTreeSet<usize>)> {
        let arguments = self.exact_call_arguments(arguments, facts).ok()?;
        let context = self.context_for(DefinitionRef::Function(callee), arguments).ok()?;
        let summary = self.function(callee, &context);
        let item = summary.certified()?;
        let Range::Exact(value) = item.complete_return()? else { return None };
        Some((value.clone(), item.input_dependencies().clone()))
    }

    fn acyclic_function_calls(&self, start: FunctionId) -> bool {
        let mut stack = vec![Visit::Enter(start)];
        let mut active = BTreeSet::new();
        let mut done = BTreeSet::new();
        while let Some(visit) = stack.pop() {
            match visit {
                Visit::Enter(id) => {
                    if !self.enter_function(id, &mut active, &done, &mut stack) {
                        return false;
                    }
                }
                Visit::Leave(id) => {
                    active.remove(&id);
                    done.insert(id);
                }
            }
        }
        true
    }

    fn enter_function(
        &self,
        id: FunctionId,
        active: &mut BTreeSet<FunctionId>,
        done: &BTreeSet<FunctionId>,
        stack: &mut Vec<Visit>,
    ) -> bool {
        const MAX_FUNCTIONS: usize = 64;
        if done.contains(&id) {
            return true;
        }
        if active.contains(&id) || active.len() + done.len() >= MAX_FUNCTIONS {
            return false;
        }
        active.insert(id);
        stack.push(Visit::Leave(id));
        let owner = CallOwner::Definition(DefinitionRef::Function(id));
        for site in self.graph().calls_from(owner) {
            if let Some(DefinitionRef::Function(callee)) = site.resolved() {
                stack.push(Visit::Enter(callee));
            }
        }
        true
    }
}
