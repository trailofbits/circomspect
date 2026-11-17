use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{FlowGraph, NodeId};
use parser::hir::{DefinitionRef, ExprId, HirProject};
use parser::hir::{SymbolId, SymbolKind};
use parser::frontend::Span;

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::{AnalysisFacts, FactBlocker, VisitAccesses};
use crate::interprocedural::{ArgumentValue, CallBlocker, ContextEvidence, SummaryBlocker};
use crate::rules::AbstentionReason;

#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) enum CoverageKind {
    MissingContext,
    InternalError,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CoverageExplanation {
    pub kind: CoverageKind,
    pub span: Span,
    pub message: String,
    pub help: String,
}

pub(super) struct CoverageContext<'a, 'facts> {
    pub hir: &'a HirProject,
    pub facts: Option<&'a AnalysisFacts<'facts>>,
    pub evidence: Option<&'a ContextEvidence>,
    pub span: Span,
}

impl CoverageContext<'_, '_> {
    pub(super) fn rule(&self, reason: &AbstentionReason) -> Vec<CoverageExplanation> {
        match reason {
            AbstentionReason::LocalFacts(reasons) => self.facts(reasons),
            AbstentionReason::Summary(reasons) => {
                reasons.iter().flat_map(|reason| self.summary(reason)).collect()
            }
            AbstentionReason::Call(reasons) => {
                reasons.iter().flat_map(|reason| self.call(reason)).collect()
            }
            AbstentionReason::SymbolicParameters => self.symbolic_expression(),
            AbstentionReason::UnsupportedConstruct | AbstentionReason::IncompleteDefinition => {
                Vec::new()
            }
        }
    }

    pub(super) fn summary(&self, reason: &SummaryBlocker) -> Vec<CoverageExplanation> {
        match reason {
            SummaryBlocker::LocalFacts(reasons) => {
                // Summary blockers can contain node indices from a callee's CFG.
                Self { facts: None, ..*self }.facts(reasons)
            }
            SummaryBlocker::UnprovenArgument(expression) => {
                self.parameters(*expression).into_iter().collect()
            }
            SummaryBlocker::ForeignDefinition
            | SummaryBlocker::WrongContext
            | SummaryBlocker::LocalAnalysis(_) => vec![self.internal()],
            SummaryBlocker::UnsupportedContext
            | SummaryBlocker::UnsupportedCallForm
            | SummaryBlocker::ExternalSummary
            | SummaryBlocker::ContextBudget
            | SummaryBlocker::RecursiveCycle
            | SummaryBlocker::IncompleteDefinition
            | SummaryBlocker::ForeignCall
            | SummaryBlocker::WrongArity { .. }
            | SummaryBlocker::InvalidAssignment(_)
            | SummaryBlocker::InvalidValueUse(_)
            | SummaryBlocker::WrongInstance
            | SummaryBlocker::DuplicateInstance
            | SummaryBlocker::SymbolicInstance
            | SummaryBlocker::MissingInputBinding
            | SummaryBlocker::DuplicateInputBinding
            | SummaryBlocker::WitnessOnlyInput
            | SummaryBlocker::MissingReturn => Vec::new(),
        }
    }

    fn facts(&self, reasons: &BTreeSet<FactBlocker>) -> Vec<CoverageExplanation> {
        reasons.iter().flat_map(|reason| self.fact(reason)).collect()
    }

    fn fact(&self, reason: &FactBlocker) -> Vec<CoverageExplanation> {
        let result = match reason {
            FactBlocker::DeferredShape(expression) | FactBlocker::OpaqueExpression(expression) => {
                self.parameters(*expression)
            }
            FactBlocker::DeferredControl(node) => self.control(*node),
            FactBlocker::ForeignQuery | FactBlocker::ForeignDefinition => Some(self.internal()),
            FactBlocker::Budget(_)
            | FactBlocker::OpaqueNode(_, _)
            | FactBlocker::AggregateConstraint(_)
            | FactBlocker::UnsupportedRelation(_)
            | FactBlocker::OpaqueEdge(_, _)
            | FactBlocker::ExternalSummary
            | FactBlocker::AggregateAccess
            | FactBlocker::WitnessWrite(_, _)
            | FactBlocker::SignalRead(_, _)
            | FactBlocker::MissingExit => None,
        };
        result.into_iter().collect()
    }

    pub(super) fn call(&self, reason: &CallBlocker) -> Vec<CoverageExplanation> {
        match reason {
            CallBlocker::LocalFacts(reasons) => self.facts(reasons),
            CallBlocker::ForeignSite | CallBlocker::ForeignDefinition => vec![self.internal()],
            CallBlocker::UnresolvedTarget
            | CallBlocker::ProvisionalSite
            | CallBlocker::MissingExpression => Vec::new(),
        }
    }

    fn control(&self, id: NodeId) -> Option<CoverageExplanation> {
        let CfgNodeKind::Branch { condition, .. } = &self.facts?.cfg().node(id)?.kind else {
            return None;
        };
        let mut result = self.parameters(*condition)?;
        result.span = self.node_span(id);
        Some(result)
    }

    fn symbolic_expression(&self) -> Vec<CoverageExplanation> {
        let Some(facts) = self.facts else { return Vec::new() };
        let expression = facts
            .cfg()
            .evaluated_expressions()
            .find(|id| self.hir.expression(*id).is_some_and(|item| item.span == self.span));
        expression.and_then(|id| self.parameters(id)).into_iter().collect()
    }

    fn parameters(&self, expression: ExprId) -> Option<CoverageExplanation> {
        let mut parameters = self.missing_parameters();
        if parameters.is_empty() {
            return None;
        }
        let dependencies = self.dependencies(expression);
        parameters.retain(|(symbol, _)| dependencies.contains(symbol));
        if parameters.is_empty() {
            return None;
        }
        let names: Vec<_> = parameters.iter().map(|(_, name)| format!("`{name}`")).collect();
        let names = names.join(", ");
        let plural = if parameters.len() == 1 { "parameter" } else { "parameters" };
        let message = format!("This check depends on unknown {plural} {names}.");
        let span = self.hir.expression(expression).map_or(self.span, |item| item.span);
        Some(explanation(
            CoverageKind::MissingContext,
            span,
            &message,
            &format!(
                "Analyze a caller with concrete values for {names} to check that instantiation."
            ),
        ))
    }

    fn missing_parameters(&self) -> Vec<(SymbolId, &str)> {
        let Some(evidence) = self.evidence else { return Vec::new() };
        let parameters = match evidence.context().definition() {
            DefinitionRef::Function(id) => {
                self.hir.function(id).map(|item| item.parameters.as_slice())
            }
            DefinitionRef::Template(id) => {
                self.hir.template(id).map(|item| item.parameters.as_slice())
            }
            DefinitionRef::Bus(id) => self.hir.bus(id).map(|item| item.parameters.as_slice()),
        };
        let Some(parameters) = parameters else { return Vec::new() };
        let mut missing = Vec::new();
        for (parameter, argument) in parameters.iter().zip(evidence.context().arguments()) {
            if unknown_argument(argument) {
                if let Some(symbol) = self.hir.symbol(*parameter) {
                    missing.push((*parameter, symbol.name.as_str()));
                }
            }
        }
        missing
    }

    fn dependencies(&self, expression: ExprId) -> BTreeSet<SymbolId> {
        let mut reached = BTreeSet::new();
        expression.visit_accesses(self.hir, &mut |path| {
            reached.insert(path.root);
        });
        if !reached.iter().any(|id| {
            self.hir.symbol(*id).is_some_and(|symbol| symbol.kind == SymbolKind::Variable)
        }) {
            return reached;
        }
        let Some(facts) = self.facts else { return reached };
        let assignments = self.assignments(facts);
        let mut pending: Vec<_> = reached.iter().copied().collect();
        while let Some(symbol) = pending.pop() {
            let Some(values) = assignments.get(&symbol) else { continue };
            if values.len() != 1 {
                continue;
            }
            let Some(value) = values.first() else { continue };
            value.visit_accesses(self.hir, &mut |path| {
                if reached.insert(path.root) {
                    pending.push(path.root);
                }
            });
        }
        reached
    }

    fn assignments(&self, facts: &AnalysisFacts<'_>) -> BTreeMap<SymbolId, BTreeSet<ExprId>> {
        let mut assignments = BTreeMap::<SymbolId, BTreeSet<ExprId>>::new();
        for id in facts.cfg().nodes() {
            if facts.certified_dead_node(*id) {
                continue;
            }
            let Some(
                CfgNodeKind::Assignment { target, value, .. }
                | CfgNodeKind::DeferredAssignment { target, value, .. }
                | CfgNodeKind::OpaqueAssignment { target, value, .. },
            ) = facts.cfg().node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            if self.hir.symbol(target.root).is_some_and(|item| item.kind == SymbolKind::Variable) {
                assignments.entry(target.root).or_default().insert(*value);
            }
        }
        assignments
    }

    fn node_span(&self, id: NodeId) -> Span {
        self.facts
            .and_then(|facts| facts.cfg().node(id))
            .and_then(|node| node.origin)
            .map_or(self.span, |origin| origin.span)
    }

    fn internal(&self) -> CoverageExplanation {
        explanation(
            CoverageKind::InternalError,
            self.span,
            "The analyzer encountered an inconsistent internal analysis context.",
            "Report this analyzer failure with a minimal reproducible Circom input.",
        )
    }
}

fn unknown_argument(argument: &ArgumentValue) -> bool {
    match argument {
        ArgumentValue::Symbolic(_) => true,
        ArgumentValue::Array(values) => values.iter().any(unknown_argument),
        ArgumentValue::Bus(fields) => fields.values().any(unknown_argument),
        ArgumentValue::Scalar(_) => false,
    }
}

fn explanation(kind: CoverageKind, span: Span, message: &str, help: &str) -> CoverageExplanation {
    CoverageExplanation { kind, span, message: message.into(), help: help.into() }
}
