//! Exact internal signals without generated constraint incidence.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use parser::hir::{AccessPath, DefinitionRef, SymbolId, SymbolKind};
use parser::new_frontend::Span;

use crate::hir_cfg::{Constraint, CfgNode, CfgNodeKind};
use crate::hir_facts::{AccessKey, Incidence, VisitAccesses};
use crate::new_rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult};
use crate::new_rules::constraints::abstain;

pub(super) struct UnconstrainedSignal;

impl Rule for UnconstrainedSignal {
    fn kind(&self) -> RuleKind {
        RuleKind::UnconstrainedSignal
    }

    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
        let mut result = RuleResult::default();
        let DefinitionRef::Template(_) = context.call_context().definition() else { return result };
        let mut emitted = BTreeSet::new();
        for id in context.facts().cfg().nodes() {
            let Some(node) = context.facts().cfg().node(*id) else { continue };
            for path in candidates(context, node) {
                if internal_signal(context, &path) {
                    inspect(context, node, &path, &mut result, &mut emitted);
                }
            }
        }
        result
    }
}

fn candidates(context: &RuleContext<'_, '_, '_>, node: &CfgNode) -> Vec<AccessPath> {
    let mut paths = Vec::new();
    match &node.kind {
        CfgNodeKind::Declaration { symbol } => {
            if let Some(path) = declaration_path(context, *symbol) {
                paths.push(path);
            }
        }
        CfgNodeKind::Evaluate(expression) => {
            expression.visit_accesses(context.hir(), &mut |path| paths.push(path.clone()));
        }
        CfgNodeKind::Witness { target, .. }
        | CfgNodeKind::Assignment { target, .. }
        | CfgNodeKind::DeferredAssignment { target, .. }
        | CfgNodeKind::OpaqueAssignment { target, .. }
        | CfgNodeKind::Update { target, .. } => paths.push(target.clone()),
        CfgNodeKind::Constraint(Constraint::Assignment { target, .. }) => {
            paths.push(target.clone());
        }
        CfgNodeKind::Constraint(Constraint::Equality { .. })
        | CfgNodeKind::Entry
        | CfgNodeKind::Exit
        | CfgNodeKind::LoopHeader
        | CfgNodeKind::Branch { .. }
        | CfgNodeKind::Instantiate { .. }
        | CfgNodeKind::Return(_)
        | CfgNodeKind::Assert { .. }
        | CfgNodeKind::DeferredAssert { .. }
        | CfgNodeKind::Log
        | CfgNodeKind::Opaque(_)
        | CfgNodeKind::OpaqueEquality { .. } => {}
    }
    paths
}

fn declaration_path(context: &RuleContext<'_, '_, '_>, id: SymbolId) -> Option<AccessPath> {
    let symbol = context.hir().symbol(id)?;
    Some(AccessPath {
        root: id,
        terminal: id,
        steps: Vec::new(),
        component_input: false,
        component_output: false,
        span: symbol.span,
    })
}

fn internal_signal(context: &RuleContext<'_, '_, '_>, path: &AccessPath) -> bool {
    if path.root != path.terminal {
        return false;
    }
    let Some(symbol) = context.hir().symbol(path.root) else { return false };
    symbol.kind == SymbolKind::Signal
        && !context
            .hir()
            .ports()
            .iter()
            .any(|port| port.symbol == path.root && port.direction.is_some())
}

fn inspect(
    context: &RuleContext<'_, '_, '_>,
    node: &CfgNode,
    path: &AccessPath,
    result: &mut RuleResult,
    emitted: &mut BTreeSet<AccessKey>,
) {
    if !reachable(context, node, path.span, result) {
        return;
    }
    let key = context.facts().exact_access_key(path);
    let Some(key) = key.certified() else {
        let reason = AbstentionReason::LocalFacts(key.unavailable().cloned().unwrap_or_default());
        abstain(context, result, RuleKind::UnconstrainedSignal, path.span, reason);
        return;
    };
    let incidence = context.template_internal_signal_incidence(path);
    match incidence.certified() {
        Some(Incidence::Zero) => {
            if emitted.insert(key.clone()) {
                result.add_finding(context.finding(
                    RuleKind::UnconstrainedSignal,
                    "No generated constraint depends on this exact internal signal path.".into(),
                    path.span,
                    "Internal signal with zero generated-constraint incidence".into(),
                ));
            }
        }
        Some(Incidence::Must) => {}
        Some(Incidence::May) => abstain(
            context,
            result,
            RuleKind::UnconstrainedSignal,
            path.span,
            AbstentionReason::UnsupportedConstruct,
        ),
        None => {
            let reason =
                AbstentionReason::Summary(incidence.unavailable().cloned().unwrap_or_default());
            abstain(context, result, RuleKind::UnconstrainedSignal, path.span, reason);
        }
    }
}

fn reachable(
    context: &RuleContext<'_, '_, '_>,
    node: &CfgNode,
    span: Span,
    result: &mut RuleResult,
) -> bool {
    let reachable = context.facts().reachable_node(node.id);
    if let Some(value) = reachable.certified() {
        *value
    } else {
        let reason =
            AbstentionReason::LocalFacts(reachable.unavailable().cloned().unwrap_or_default());
        abstain(context, result, RuleKind::UnconstrainedSignal, span, reason);
        false
    }
}
