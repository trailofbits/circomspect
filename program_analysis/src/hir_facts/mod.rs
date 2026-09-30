//! Constraint provenance and certified local facts over the checked HIR CFG.

mod access;
mod field;
mod forward;

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{EdgeId, FlowGraph, GraphError, NodeId};
use abstract_interpretation::solver::{solve, Blocker, Forward, SolveResult};
use parser::hir::{AccessPath, ExprId, ExprKind, HirProject};

use crate::hir_cfg::{CfgNodeKind, DefinitionCfg};
use access::key_for_path;
use forward::{ForwardAnalysis, ForwardState};

pub use access::{AccessKey, AccessKeyStep, IndexKey};
pub use field::{FieldContext, FieldValue};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Fact<T> {
    Certified(T),
    Unavailable(BTreeSet<FactBlocker>),
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FactBlocker {
    Budget(NodeId),
    OpaqueNode(NodeId, String),
    OpaqueEdge(EdgeId, String),
    ExternalSummary,
    MissingExit,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Incidence {
    Zero,
    May,
    Must,
}

type ForwardResult = SolveResult<NodeId, EdgeId, ForwardState, String>;

/// Local facts retain the solver result privately so reporting queries cannot
/// accidentally consume provisional states without a closure check.
pub struct AnalysisFacts<'a> {
    hir: &'a HirProject,
    cfg: &'a DefinitionCfg,
    field: &'a FieldContext,
    forward: ForwardResult,
}

/// Compute local facts. External summaries are unavailable until Phase 5.
pub fn analyze<'a>(
    hir: &'a HirProject,
    cfg: &'a DefinitionCfg,
    field: &'a FieldContext,
    budget: Option<usize>,
) -> Result<AnalysisFacts<'a>, GraphError<NodeId, EdgeId>> {
    let forward = solve::<_, _, Forward>(cfg, &ForwardAnalysis { hir, field }, budget)?;
    Ok(AnalysisFacts { hir, cfg, field, forward })
}

impl AnalysisFacts<'_> {
    /// Whether a local access can occur in a generated constraint.
    pub fn incidence(&self, path: &AccessPath) -> Fact<Incidence> {
        let blockers = self.blockers_for(path);
        if !blockers.is_empty() {
            return Fact::Unavailable(blockers);
        }
        let Some(state) = self.exit_state() else {
            return Fact::Unavailable(BTreeSet::from([FactBlocker::MissingExit]));
        };
        let Some((may, must)) = state.constraints() else {
            return Fact::Certified(Incidence::Zero);
        };
        let query = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        let must_match = must.iter().any(|site| self.site_touches(*site, &query, true));
        let may_match = may.iter().any(|site| self.site_touches(*site, &query, false));
        let value = if must_match {
            Incidence::Must
        } else if may_match {
            Incidence::May
        } else {
            Incidence::Zero
        };
        Fact::Certified(value)
    }

    /// An exact value proved by a generated equality on every reachable path.
    pub fn constraint_fixed(&self, path: &AccessPath) -> Fact<Option<FieldValue>> {
        let blockers = self.blockers_for(path);
        if !blockers.is_empty() {
            return Fact::Unavailable(blockers);
        }
        let Some(state) = self.exit_state() else {
            return Fact::Unavailable(BTreeSet::from([FactBlocker::MissingExit]));
        };
        let Some((_, must)) = state.constraints() else {
            return Fact::Certified(None);
        };
        let query = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        let values: BTreeSet<_> =
            must.iter().filter_map(|site| self.site_fixed_value(*site, &query)).collect();
        Fact::Certified((values.len() == 1).then(|| values.into_iter().next()).flatten())
    }

    fn exit_state(&self) -> Option<&ForwardState> {
        let facts = match &self.forward {
            SolveResult::Complete(facts) => facts.get(&self.cfg.exit),
            SolveResult::Incomplete { provisional_facts, .. } => {
                provisional_facts.get(&self.cfg.exit)
            }
        }?;
        facts.output.as_ref()
    }

    fn site_state(&self, id: NodeId) -> Option<&ForwardState> {
        let facts = match &self.forward {
            SolveResult::Complete(facts) => facts.get(&id),
            SolveResult::Incomplete { provisional_facts, .. } => provisional_facts.get(&id),
        }?;
        facts.input.as_ref()
    }

    fn site_touches(&self, id: NodeId, query: &AccessKey, exact: bool) -> bool {
        let Some(node) = self.cfg.node(id) else { return false };
        let variables = self.site_state(id).and_then(ForwardState::variables);
        let empty = BTreeMap::new();
        let variables = variables.unwrap_or(&empty);
        let CfgNodeKind::Constraint { target, left, right } = &node.kind else { return false };
        target.as_ref().is_some_and(|path| {
            let key = key_for_path(self.hir, self.field, path, variables);
            if exact {
                key.exact_alias(query)
            } else {
                key.may_alias(query)
            }
        }) || self.expr_touches(*left, query, variables, exact)
            || right.is_some_and(|id| self.expr_touches(id, query, variables, exact))
    }

    fn expr_touches(
        &self,
        id: ExprId,
        query: &AccessKey,
        variables: &BTreeMap<parser::hir::SymbolId, FieldValue>,
        exact: bool,
    ) -> bool {
        let Some(expr) = self.hir.expression(id) else { return true };
        match &expr.kind {
            ExprKind::Access(path) => {
                let key = key_for_path(self.hir, self.field, path, variables);
                if exact {
                    key.exact_alias(query)
                } else {
                    key.may_alias(query)
                }
            }
            ExprKind::Unary { operand, .. } | ExprKind::Parallel(operand) => {
                self.expr_touches(*operand, query, variables, exact)
            }
            ExprKind::Binary { left, right, .. } => {
                self.expr_touches(*left, query, variables, exact)
                    || self.expr_touches(*right, query, variables, exact)
            }
            ExprKind::Ternary { condition, yes, no } => {
                self.expr_touches(*condition, query, variables, exact)
                    || self.expr_touches(*yes, query, variables, exact)
                    || self.expr_touches(*no, query, variables, exact)
            }
            ExprKind::Array(items) | ExprKind::Tuple(items) => {
                items.iter().any(|id| self.expr_touches(*id, query, variables, exact))
            }
            ExprKind::Call { arguments, .. } | ExprKind::AnonymousComponent { arguments, .. } => {
                arguments.iter().any(|id| self.expr_touches(*id, query, variables, exact))
            }
            ExprKind::Number(_) => false,
            ExprKind::Opaque(_) => true,
        }
    }

    fn site_fixed_value(&self, id: NodeId, query: &AccessKey) -> Option<FieldValue> {
        let node = self.cfg.node(id)?;
        let CfgNodeKind::Constraint { target, left, right } = &node.kind else { return None };
        let variables = self.site_state(id)?.variables()?;
        if let Some(target) = target {
            let key = key_for_path(self.hir, self.field, target, variables);
            return key
                .exact_alias(query)
                .then(|| forward::eval_expression(self.hir, self.field, *left, variables))
                .flatten();
        }
        let right = right.as_ref()?;
        self.equality_side(*left, *right, query, variables)
            .or_else(|| self.equality_side(*right, *left, query, variables))
    }

    fn equality_side(
        &self,
        access: ExprId,
        value: ExprId,
        query: &AccessKey,
        variables: &BTreeMap<parser::hir::SymbolId, FieldValue>,
    ) -> Option<FieldValue> {
        let expr = self.hir.expression(access)?;
        let ExprKind::Access(path) = &expr.kind else { return None };
        let key = key_for_path(self.hir, self.field, path, variables);
        key.exact_alias(query)
            .then(|| forward::eval_expression(self.hir, self.field, value, variables))
            .flatten()
    }

    fn blockers_for(&self, path: &AccessPath) -> BTreeSet<FactBlocker> {
        let mut blockers = BTreeSet::new();
        if self.hir.components().iter().any(|item| item.symbol == path.root) {
            blockers.insert(FactBlocker::ExternalSummary);
        }
        let SolveResult::Incomplete { blockers: solver_blockers, .. } = &self.forward else {
            return blockers;
        };
        for blocker in solver_blockers {
            match blocker {
                Blocker::PendingNode(node) => {
                    blockers.insert(FactBlocker::Budget(*node));
                }
                Blocker::OpaqueEdge { edge, reason } => {
                    blockers.insert(FactBlocker::OpaqueEdge(*edge, reason.clone()));
                }
                Blocker::OpaqueNode { node, reason } if self.opaque_relevant(*node, path) => {
                    blockers.insert(FactBlocker::OpaqueNode(*node, reason.clone()));
                }
                Blocker::OpaqueNode { .. } => {}
            }
        }
        blockers
    }

    fn opaque_relevant(&self, node_id: NodeId, path: &AccessPath) -> bool {
        let Some(node) = self.cfg.node(node_id) else { return true };
        if let CfgNodeKind::Opaque(_) = &node.kind {
            return true;
        }
        let Some(origin) = node.origin else { return true };
        let Some(effect) =
            self.hir.block(origin.block).and_then(|block| block.effects.get(origin.effect_index))
        else {
            return true;
        };
        match effect {
            parser::hir::Effect::WitnessAssignment { target, .. }
            | parser::hir::Effect::ConstraintAssignment { target, .. }
            | parser::hir::Effect::VariableAssignment { target, .. }
            | parser::hir::Effect::ComponentInstantiation { target, .. } => {
                target.root == path.root
            }
            _ => true,
        }
    }
}
