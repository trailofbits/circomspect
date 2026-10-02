//! Complete exact call results permitted to specialize one definition's local transfer.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use parser::hir::{CallTarget, DefinitionRef, ExprKind, FunctionId};

use crate::call_evidence::ExactCallResults;
use crate::hir_cfg::{build_cfg_with_exact_calls, CfgNodeKind, DefinitionCfg};
use crate::hir_facts::{AnalysisFacts, Range};
use crate::hir_facts::{analyze_with_scalar_calls, FieldContext, FieldValue};
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
        const MAX_REFINEMENTS: usize = 64;
        let field = FieldContext::for_curve(self.curve().clone());
        let mut calls = ExactCallResults::empty(self.hir(), definition, self.curve().clone());
        for _ in 0..MAX_REFINEMENTS {
            let cfg = build_cfg_with_exact_calls(self.hir(), definition, &calls)
                .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
            let facts =
                analyze_with_scalar_calls(self.hir(), &cfg, &field, parameters.clone(), &calls)
                    .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
            let discovered = self.exact_call_results(definition, &facts);
            let mut next = calls.clone();
            let changed =
                next.merge(&discovered).map_err(|()| SummaryBlocker::UnsupportedContext)?;
            if !changed {
                self.check_exact_assignment_shapes(&cfg, &facts)?;
                return work(&cfg, &facts);
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

    pub(super) fn exact_call_results(
        &self,
        definition: DefinitionRef,
        facts: &AnalysisFacts<'_>,
    ) -> ExactCallResults {
        let mut results = ExactCallResults::empty(self.hir(), definition, self.curve().clone());
        if facts.definition() != definition
            || self.hir().identity() != facts.hir().identity()
            || self.curve() != facts.curve()
        {
            return results;
        }
        let owner = CallOwner::Definition(definition);
        for site in self.graph().calls_from(owner) {
            if site.provenance == CallProvenance::Unattached {
                continue;
            }
            let Some(DefinitionRef::Function(callee)) = site.resolved() else { continue };
            if !self.acyclic_function_calls(callee) {
                continue;
            }
            let Some(expression) = site.expression else { continue };
            if facts.reachable_expression(expression).certified() != Some(&true) {
                continue;
            }
            let Some(ExprKind::Call { target: CallTarget::Function(id), arguments }) =
                self.hir().expression(expression).map(|expr| &expr.kind)
            else {
                continue;
            };
            if *id != callee {
                continue;
            }
            let Ok(arguments) = self.exact_call_arguments(arguments, facts) else { continue };
            let Ok(context) = self.context_for(DefinitionRef::Function(callee), arguments) else {
                continue;
            };
            let summary = self.function(callee, &context);
            let Some(item) = summary.certified() else { continue };
            let Some(Range::Exact(value)) = item.complete_return() else {
                continue;
            };
            results.insert(expression, value.clone(), item.input_dependencies().clone());
        }
        results
    }

    fn acyclic_function_calls(&self, start: FunctionId) -> bool {
        const MAX_FUNCTIONS: usize = 64;
        let mut stack = vec![Visit::Enter(start)];
        let mut active = BTreeSet::new();
        let mut done = BTreeSet::new();
        while let Some(visit) = stack.pop() {
            match visit {
                Visit::Enter(id) => {
                    if done.contains(&id) {
                        continue;
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
                }
                Visit::Leave(id) => {
                    active.remove(&id);
                    done.insert(id);
                }
            }
        }
        true
    }
}
