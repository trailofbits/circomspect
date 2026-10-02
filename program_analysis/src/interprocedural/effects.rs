use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{IndexedGraph, NodeId, FlowGraph};
use abstract_interpretation::lattice::{Lattice, Set};
use abstract_interpretation::solver::{
    solve, DataflowAnalysis, Forward, SolveResult, Transfer, TransferOutcome,
};
use parser::hir::{DefinitionRef, FunctionId};
use parser::new_frontend::AssignmentOperator;

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::Range;

use super::summary::certified;
use super::{
    CallBlocker, CallContext, CallOwner, CallReachability, ProjectSummaries, SummaryBlocker,
    SummaryFact,
};

/// Observable effects permitted in a checked Circom function.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FunctionEffect {
    Assert,
    Log,
}

/// May-effects of every reachable call in one function context.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionEffects(Set<FunctionEffect>);

impl FunctionEffects {
    /// Whether the complete reachable function context has no observable effects.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.iter().next().is_none()
    }

    #[must_use]
    pub fn contains(&self, effect: FunctionEffect) -> bool {
        self.0.iter().any(|item| *item == effect)
    }
}

struct EffectRecord {
    local: Set<FunctionEffect>,
    callees: BTreeSet<CallContext>,
}

enum EffectNode {
    Source,
    Context(Set<FunctionEffect>),
}

struct EffectEdge;
struct EffectAnalysis;

impl DataflowAnalysis<IndexedGraph<EffectNode, EffectEdge>> for EffectAnalysis {
    type State = Set<FunctionEffect>;
    type Reason = ();

    fn boundary(&self, _: NodeId) -> Self::State {
        Set::bottom()
    }
}

impl Transfer<EffectAnalysis, Set<FunctionEffect>, ()> for EffectNode {
    fn apply(
        &self,
        _: &EffectAnalysis,
        input: &Set<FunctionEffect>,
    ) -> TransferOutcome<Set<FunctionEffect>, ()> {
        let mut output = input.clone();
        if let Self::Context(local) = self {
            output.join_assign(local);
        }
        TransferOutcome::Known(output)
    }
}

impl Transfer<EffectAnalysis, Set<FunctionEffect>, ()> for EffectEdge {
    fn apply(
        &self,
        _: &EffectAnalysis,
        input: &Set<FunctionEffect>,
    ) -> TransferOutcome<Set<FunctionEffect>, ()> {
        TransferOutcome::Known(input.clone())
    }
}

impl ProjectSummaries<'_> {
    /// Solve reachable function effects to a least fixed point, including recursive SCCs.
    pub fn function_effects(
        &self,
        id: FunctionId,
        context: &CallContext,
    ) -> SummaryFact<FunctionEffects> {
        if context.definition() != DefinitionRef::Function(id) {
            return SummaryFact::from_result(Err(SummaryBlocker::WrongContext));
        }
        if self.hir().function(id).is_none() {
            return SummaryFact::from_result(Err(SummaryBlocker::ForeignDefinition));
        }
        if let Err(blocker) = self.check_context(context) {
            return SummaryFact::from_result(Err(blocker));
        }
        self.caches.effects.get_or_compute(context.clone(), || {
            SummaryFact::from_result(self.compute_function_effects(context))
        })
    }

    fn compute_function_effects(
        &self,
        context: &CallContext,
    ) -> Result<FunctionEffects, SummaryBlocker> {
        const MAX_CONTEXTS: usize = 64;
        let mut records = BTreeMap::new();
        let mut pending = vec![context.clone()];
        while let Some(next) = pending.pop() {
            if records.contains_key(&next) {
                continue;
            }
            if records.len() >= MAX_CONTEXTS {
                return Err(SummaryBlocker::ContextBudget);
            }
            let record = self.effect_record(&next)?;
            pending.extend(record.callees.iter().cloned());
            records.insert(next, record);
        }
        solve_effects(&records, context)
    }

    fn effect_record(&self, context: &CallContext) -> Result<EffectRecord, SummaryBlocker> {
        let DefinitionRef::Function(id) = context.definition() else {
            return Err(SummaryBlocker::WrongContext);
        };
        self.with_local_function(id, context, |_, cfg, facts| {
            let mut local = Set::bottom();
            for id in cfg.nodes() {
                let node = cfg
                    .node(*id)
                    .ok_or(SummaryBlocker::LocalAnalysis("missing effect graph node".into()))?;
                let effect = match &node.kind {
                    CfgNodeKind::Assert { .. } => Some(Ok(FunctionEffect::Assert)),
                    CfgNodeKind::DeferredAssert { condition } => {
                        let fact = match facts.range(*condition).certified() {
                            Some(Range::Exact(_)) => Ok(FunctionEffect::Assert),
                            Some(Range::Canonical | Range::Unreachable) | None => {
                                Err(SummaryBlocker::UnsupportedContext)
                            }
                        };
                        Some(fact)
                    }
                    CfgNodeKind::Log => Some(Ok(FunctionEffect::Log)),
                    CfgNodeKind::Assignment { operator, .. }
                        if *operator != AssignmentOperator::Assign =>
                    {
                        Some(Err(SummaryBlocker::UnsupportedContext))
                    }
                    CfgNodeKind::DeferredAssignment { operator, .. }
                        if *operator != AssignmentOperator::Assign
                            || !facts.resolved_deferred_assignment(*id) =>
                    {
                        Some(Err(SummaryBlocker::UnsupportedContext))
                    }
                    CfgNodeKind::Opaque(_)
                    | CfgNodeKind::OpaqueAssignment { .. }
                    | CfgNodeKind::OpaqueEquality { .. }
                    | CfgNodeKind::Instantiate { .. }
                    | CfgNodeKind::Witness { .. }
                    | CfgNodeKind::Constraint { .. } => Some(Err(SummaryBlocker::ExternalSummary)),
                    _ => None,
                };
                let Some(effect) = effect else { continue };
                if !*certified(&facts.reachable_node(*id))? {
                    continue;
                }
                local.insert(effect?);
            }
            let mut callees = BTreeSet::new();
            let owner = CallOwner::Definition(DefinitionRef::Function(id));
            for site in self.graph().calls_from(owner) {
                let context = match self.graph().reachable_call(site.id(), facts) {
                    CallReachability::Unreachable => continue,
                    CallReachability::Reachable(call) => {
                        if let DefinitionRef::Function(_) = call.callee() {
                            self.call_context(&call, facts)?
                        } else {
                            return Err(SummaryBlocker::ExternalSummary);
                        }
                    }
                    CallReachability::Unavailable(CallBlocker::ProvisionalSite) => {
                        self.exact_site_context(site, facts)?
                    }
                    CallReachability::Unavailable(_) => {
                        return Err(SummaryBlocker::ExternalSummary)
                    }
                };
                callees.insert(context);
            }
            Ok(EffectRecord { local, callees })
        })
    }
}

fn solve_effects(
    records: &BTreeMap<CallContext, EffectRecord>,
    root: &CallContext,
) -> Result<FunctionEffects, SummaryBlocker> {
    let mut nodes = vec![EffectNode::Source];
    let mut indices = BTreeMap::new();
    for (context, record) in records {
        let id = NodeId::new(nodes.len());
        indices.insert(context.clone(), id);
        nodes.push(EffectNode::Context(record.local.clone()));
    }
    let mut edges = Vec::new();
    for (context, record) in records {
        let caller = *indices.get(context).ok_or(SummaryBlocker::WrongContext)?;
        edges.push((NodeId::new(0), caller, EffectEdge));
        for callee in &record.callees {
            let callee = *indices.get(callee).ok_or(SummaryBlocker::WrongContext)?;
            edges.push((callee, caller, EffectEdge));
        }
    }
    let root = *indices.get(root).ok_or(SummaryBlocker::WrongContext)?;
    let graph = IndexedGraph::new(nodes, edges, vec![NodeId::new(0)], vec![root])
        .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
    let result = solve::<_, _, Forward>(&graph, &EffectAnalysis, Some(100_000))
        .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
    let SolveResult::Complete(facts) = result else {
        return Err(SummaryBlocker::ContextBudget);
    };
    let effects = facts
        .get(&root)
        .and_then(|item| item.output.as_ref())
        .ok_or(SummaryBlocker::LocalAnalysis("missing root effect state".into()))?;
    Ok(FunctionEffects(effects.clone()))
}

#[cfg(test)]
mod tests {
    use abstract_interpretation::lattice::{Lattice, Set};
    use abstract_interpretation::solver::{Transfer, TransferOutcome};

    use super::{EffectAnalysis, EffectEdge, EffectNode, FunctionEffect};

    #[test]
    fn production_effect_transfers_are_monotone() {
        let mut states = vec![Set::bottom()];
        let mut assertion = Set::bottom();
        assertion.insert(FunctionEffect::Assert);
        states.push(assertion.clone());
        let mut log = Set::bottom();
        log.insert(FunctionEffect::Log);
        states.push(log.clone());
        log.join_assign(&assertion);
        states.push(log);
        for left in &states {
            for right in &states {
                if !left.leq(right) {
                    continue;
                }
                for node in [EffectNode::Source, EffectNode::Context(assertion.clone())] {
                    let TransferOutcome::Known(left_out) = node.apply(&EffectAnalysis, left) else {
                        panic!("known effect transfer")
                    };
                    let TransferOutcome::Known(right_out) = node.apply(&EffectAnalysis, right)
                    else {
                        panic!("known effect transfer")
                    };
                    assert!(left_out.leq(&right_out));
                }
                let TransferOutcome::Known(left_out) = EffectEdge.apply(&EffectAnalysis, left)
                else {
                    panic!("known edge transfer")
                };
                let TransferOutcome::Known(right_out) = EffectEdge.apply(&EffectAnalysis, right)
                else {
                    panic!("known edge transfer")
                };
                assert!(left_out.leq(&right_out));
            }
        }
    }
}
