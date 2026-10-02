//! Direct syntax and maintainability warning family.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{EdgeId, FlowGraph, NodeId};
use parser::hir::{ControlGuard, DefinitionRef};
use parser::new_frontend::Span;

use crate::hir_cfg::{CfgNodeKind, DefinitionCfg, EdgeKind};
use crate::hir_facts::{AnalysisFacts, FactBlocker};
use crate::interprocedural::SummaryBlocker;
use crate::new_rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult, ScopedAbstention};

const MAX_COMPLEXITY: usize = 20;
const MAX_PARAMETERS: usize = 7;

pub const KINDS: &[RuleKind] = &[RuleKind::Complexity, RuleKind::TooManyArguments];

static COMPLEXITY: ComplexityRule = ComplexityRule;
static ARGUMENTS: TooManyArgumentsRule = TooManyArgumentsRule;
static RULES: [&'static dyn Rule; 2] = [&COMPLEXITY, &ARGUMENTS];

/// Direct rules enter the registry in this family's declared order.
pub fn rules() -> &'static [&'static dyn Rule] {
    &RULES
}

struct ComplexityRule;

impl Rule for ComplexityRule {
    fn kind(&self) -> RuleKind {
        RuleKind::Complexity
    }

    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
        let Some(span) = name_span(context) else { return RuleResult::default() };
        let definition = match context.validated_definition() {
            Ok(definition) => definition,
            Err(blocker) => return abstain(context, self.kind(), span, summary_reason(blocker)),
        };
        let header = definition.header();
        match reachable_complexity(context.facts()) {
            Metric::Known(value) if value > MAX_COMPLEXITY => {
                let message = format!(
                    "`{}` has cyclomatic complexity {value} (limit {MAX_COMPLEXITY}).",
                    header.name()
                );
                let mut result = RuleResult::default();
                result.add_finding(context.finding(
                    self.kind(),
                    message,
                    header.name_span(),
                    format!("Complexity is {value}."),
                ));
                result
            }
            Metric::Known(_) => RuleResult::default(),
            Metric::Blocked(blockers) => {
                abstain(context, self.kind(), span, AbstentionReason::LocalFacts(blockers))
            }
            Metric::Symbolic => {
                abstain(context, self.kind(), span, AbstentionReason::SymbolicParameters)
            }
        }
    }
}

struct TooManyArgumentsRule;

impl Rule for TooManyArgumentsRule {
    fn kind(&self) -> RuleKind {
        RuleKind::TooManyArguments
    }

    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
        let Some(span) = name_span(context) else { return RuleResult::default() };
        let header = match context.validated_header() {
            Ok(header) => header,
            Err(blocker) => return abstain(context, self.kind(), span, summary_reason(blocker)),
        };
        let count = header.parameter_count();
        if count <= MAX_PARAMETERS {
            return RuleResult::default();
        }
        let mut result = RuleResult::default();
        result.add_finding(context.finding(
            self.kind(),
            format!("`{}` declares {count} parameters (limit {MAX_PARAMETERS}).", header.name()),
            header.name_span(),
            format!("This declaration has {count} parameters."),
        ));
        result
    }
}

fn summary_reason(blocker: SummaryBlocker) -> AbstentionReason {
    AbstentionReason::Summary(BTreeSet::from([blocker]))
}

fn abstain(
    context: &RuleContext<'_, '_, '_>,
    kind: RuleKind,
    span: Span,
    reason: AbstentionReason,
) -> RuleResult {
    let mut result = RuleResult::default();
    result.add_abstention(ScopedAbstention {
        kind,
        context: context.call_context().clone(),
        span,
        reason,
    });
    result
}

fn name_span(context: &RuleContext<'_, '_, '_>) -> Option<Span> {
    match context.call_context().definition() {
        DefinitionRef::Function(id) => context.hir().function(id).map(|item| item.name_span),
        DefinitionRef::Template(id) => context.hir().template(id).map(|item| item.name_span),
        DefinitionRef::Bus(_) => None,
    }
}

enum Metric {
    Known(usize),
    Blocked(BTreeSet<FactBlocker>),
    Symbolic,
}

fn reachable_complexity(facts: &AnalysisFacts<'_>) -> Metric {
    let mut blockers = BTreeSet::new();
    let nodes = reachable_node_count(facts, &mut blockers);
    let (edges, active_edges) = reachable_edge_count(facts, &mut blockers);
    if !blockers.is_empty() {
        return Metric::Blocked(blockers);
    }
    if has_symbolic_decision(facts.cfg(), &active_edges) {
        return Metric::Symbolic;
    }
    // Every certified reachable node belongs to the single entry component, so P = 1.
    let Some(value) = edges.checked_add(2).and_then(|value| value.checked_sub(nodes)) else {
        return Metric::Blocked(BTreeSet::from([FactBlocker::MissingExit]));
    };
    Metric::Known(value)
}

fn reachable_node_count(facts: &AnalysisFacts<'_>, blockers: &mut BTreeSet<FactBlocker>) -> usize {
    let mut nodes = 0_usize;
    for id in facts.cfg().nodes() {
        let reachability = facts.reachable_node(*id);
        match reachability.certified() {
            Some(true) => nodes += 1,
            Some(false) => {}
            None => blockers.extend(reachability.unavailable().into_iter().flatten().cloned()),
        }
    }
    nodes
}

fn reachable_edge_count(
    facts: &AnalysisFacts<'_>,
    blockers: &mut BTreeSet<FactBlocker>,
) -> (usize, BTreeSet<EdgeId>) {
    let mut edges = 0_usize;
    let mut active_edges = BTreeSet::new();
    for id in facts.cfg().edges() {
        let reachability = facts.reachable_edge(*id);
        match reachability.certified() {
            Some(true) => {
                edges += 1;
                active_edges.insert(*id);
            }
            Some(false) => {}
            None => blockers.extend(reachability.unavailable().into_iter().flatten().cloned()),
        }
    }
    (edges, active_edges)
}

fn has_symbolic_decision(cfg: &DefinitionCfg, active: &BTreeSet<EdgeId>) -> bool {
    let mut arms = BTreeMap::<NodeId, (bool, bool)>::new();
    for id in active {
        let Some((source, kind)) = compile_time_arm(cfg, *id) else { continue };
        let entry = arms.entry(source).or_default();
        match kind {
            EdgeKind::True => entry.0 = true,
            EdgeKind::False => entry.1 = true,
            EdgeKind::Normal | EdgeKind::Loop | EdgeKind::Return => {}
        }
    }
    arms.values().any(|(yes, no)| *yes && *no)
}

fn compile_time_arm(cfg: &DefinitionCfg, id: EdgeId) -> Option<(NodeId, EdgeKind)> {
    let edge = cfg.edge(id)?;
    let node = cfg.node(edge.source)?;
    let CfgNodeKind::Branch { guard, .. } = node.kind else { return None };
    match guard {
        ControlGuard::CheckedCompileTime | ControlGuard::DeferredScalar => {
            Some((edge.source, edge.payload.kind))
        }
        ControlGuard::WitnessOnly => None,
    }
}
