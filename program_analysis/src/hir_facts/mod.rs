//! Constraint provenance and certified local facts over the checked HIR CFG.

mod access;
mod domains;
mod field;
mod forward;
mod liveness;
mod walk;

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{EdgeId, FlowGraph, GraphError, NodeId};
use abstract_interpretation::solver::{solve, Backward, Blocker, Forward, SolveResult};
use parser::hir::{AccessPath, DefinitionRef, ExprId, ExprKind, HirProject};

use crate::hir_cfg::{CfgNodeKind, DefinitionCfg};
use access::key_for_path;
use abstract_interpretation::lattice::Lattice;
use domains::{DegreeUpper, FieldRange};
use forward::{ForwardAnalysis, ForwardState};
use liveness::{LiveState, LivenessAnalysis};
use walk::VisitAccesses;

pub use access::{AccessKey, AccessKeyStep, IndexKey};
pub use domains::{DegreeUpper as Degree, FieldRange as Range};
pub use field::{FieldContext, FieldValue};

/// A reporting fact whose certified constructor is private to the analysis.
///
/// ```compile_fail
/// use circomspect_program_analysis::hir_facts::{Fact, Incidence};
/// let forged = Fact::known(Incidence::Zero);
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Fact<T>(FactState<T>);

#[derive(Clone, Debug, Eq, PartialEq)]
enum FactState<T> {
    Certified(T),
    Unavailable(BTreeSet<FactBlocker>),
}

impl<T> Fact<T> {
    fn known(value: T) -> Self {
        Self(FactState::Certified(value))
    }

    fn blocked(blockers: BTreeSet<FactBlocker>) -> Self {
        Self(FactState::Unavailable(blockers))
    }

    #[must_use]
    pub fn certified(&self) -> Option<&T> {
        match &self.0 {
            FactState::Certified(value) => Some(value),
            FactState::Unavailable(_) => None,
        }
    }

    #[must_use]
    pub fn unavailable(&self) -> Option<&BTreeSet<FactBlocker>> {
        match &self.0 {
            FactState::Certified(_) => None,
            FactState::Unavailable(blockers) => Some(blockers),
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum FactBlocker {
    Budget(NodeId),
    OpaqueNode(NodeId, String),
    OpaqueEdge(EdgeId, String),
    ExternalSummary,
    AggregateAccess,
    AggregateConstraint(NodeId),
    DeferredControl(NodeId),
    OpaqueExpression(ExprId),
    MissingExit,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Incidence {
    Zero,
    May,
    Must,
}

type ForwardResult = SolveResult<NodeId, EdgeId, ForwardState, String>;
type BackwardResult = SolveResult<NodeId, EdgeId, LiveState, String>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AnalysisError {
    ForeignProject,
    InvalidGraph(GraphError<NodeId, EdgeId>),
}

/// Local facts retain the solver result privately so reporting queries cannot
/// accidentally consume provisional states without a closure check.
pub struct AnalysisFacts<'a> {
    hir: &'a HirProject,
    cfg: &'a DefinitionCfg,
    field: &'a FieldContext,
    forward: ForwardResult,
    backward: BackwardResult,
}

/// Compute local facts. External summaries are unavailable until Phase 5.
pub fn analyze<'a>(
    hir: &'a HirProject,
    cfg: &'a DefinitionCfg,
    field: &'a FieldContext,
    budget: Option<usize>,
) -> Result<AnalysisFacts<'a>, AnalysisError> {
    let owned = match cfg.definition {
        DefinitionRef::Function(id) => hir.function(id).is_some(),
        DefinitionRef::Template(id) => hir.template(id).is_some(),
        DefinitionRef::Bus(id) => hir.bus(id).is_some(),
    };
    if !owned {
        return Err(AnalysisError::ForeignProject);
    }
    let forward = solve::<_, _, Forward>(cfg, &ForwardAnalysis { hir, field }, budget)
        .map_err(AnalysisError::InvalidGraph)?;
    let backward =
        solve::<_, _, Backward>(cfg, &LivenessAnalysis::new(hir, field, cfg.definition), budget)
            .map_err(AnalysisError::InvalidGraph)?;
    Ok(AnalysisFacts { hir, cfg, field, forward, backward })
}

impl AnalysisFacts<'_> {
    /// A compile-time exact value or the full canonical field range.
    pub fn range(&self, expression: ExprId) -> Fact<FieldRange> {
        let scalar_blockers = self.scalar_blockers(expression);
        if !scalar_blockers.is_empty() {
            return Fact::blocked(scalar_blockers);
        }
        let mut result = FieldRange::Unreachable;
        let mut observed = false;
        for node in self.cfg.nodes() {
            let Some(CfgNodeKind::Evaluate(id)) = self.cfg.node(*node).map(|item| &item.kind)
            else {
                continue;
            };
            if *id != expression {
                continue;
            }
            let Some(variables) = self.site_state(*node).and_then(ForwardState::variables) else {
                continue;
            };
            observed = true;
            let value = forward::eval_expression(self.hir, self.field, expression, variables)
                .map_or(FieldRange::Canonical, FieldRange::Exact);
            result.join_assign(&value);
        }
        if !observed {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        }
        let blockers = self.expression_blockers(expression);
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        Fact::known(result)
    }

    /// Upper bound on witness polynomial degree; unknown operations are unbounded.
    pub fn degree(&self, expression: ExprId) -> Fact<DegreeUpper> {
        let mut blockers = self.expression_blockers(expression);
        blockers.extend(self.scalar_blockers(expression));
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        Fact::known(self.degree_of(expression))
    }

    /// May-dependencies of a source expression, including local variable assignments.
    pub fn dependencies(&self, expression: ExprId) -> Fact<BTreeSet<AccessKey>> {
        let blockers = self.expression_blockers(expression);
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        let mut result = BTreeSet::new();
        let mut variables = BTreeSet::new();
        let complete = expression.visit_accesses(self.hir, &mut |path| {
            result.insert(key_for_path(self.hir, self.field, path, &BTreeMap::new()));
            if self
                .hir
                .symbol(path.root)
                .is_some_and(|symbol| symbol.kind == parser::hir::SymbolKind::Variable)
            {
                variables.insert(path.root);
            }
        });
        if !complete {
            return Fact::blocked(BTreeSet::from([FactBlocker::OpaqueExpression(expression)]));
        }
        let mut seen = BTreeSet::new();
        for variable in variables {
            if !self.collect_variable_paths(variable, &mut result, &mut seen) {
                return Fact::blocked(BTreeSet::from([FactBlocker::OpaqueExpression(expression)]));
            }
        }
        Fact::known(result)
    }

    fn collect_variable_paths(
        &self,
        variable: parser::hir::SymbolId,
        result: &mut BTreeSet<AccessKey>,
        seen: &mut BTreeSet<parser::hir::SymbolId>,
    ) -> bool {
        if !seen.insert(variable) {
            return true;
        }
        let mut complete = true;
        for node in self.cfg.nodes() {
            let Some(CfgNodeKind::Assignment { target, value }) =
                self.cfg.node(*node).map(|item| &item.kind)
            else {
                continue;
            };
            if target.root != variable {
                continue;
            }
            let mut nested = BTreeSet::new();
            complete &= value.visit_accesses(self.hir, &mut |path| {
                result.insert(key_for_path(self.hir, self.field, path, &BTreeMap::new()));
                if self
                    .hir
                    .symbol(path.root)
                    .is_some_and(|symbol| symbol.kind == parser::hir::SymbolKind::Variable)
                {
                    nested.insert(path.root);
                }
            });
            for child in nested {
                complete &= self.collect_variable_paths(child, result, seen);
            }
        }
        complete
    }

    fn expression_blockers(&self, expression: ExprId) -> BTreeSet<FactBlocker> {
        let mut blockers = BTreeSet::new();
        let mut uses = Vec::new();
        if !expression.visit_accesses(self.hir, &mut |path| uses.push(path.clone())) {
            blockers.insert(FactBlocker::OpaqueExpression(expression));
        }
        let mut sites: BTreeSet<_> = self
            .cfg
            .nodes()
            .iter()
            .copied()
            .filter(|node| match self.cfg.node(*node).map(|item| &item.kind) {
                Some(CfgNodeKind::Evaluate(id)) => *id == expression,
                _ => false,
            })
            .collect();
        let mut seen = BTreeSet::new();
        for path in &uses {
            if self
                .hir
                .symbol(path.root)
                .is_some_and(|symbol| symbol.kind == parser::hir::SymbolKind::Variable)
            {
                self.variable_assignment_sites(path.root, &mut sites, &mut seen);
            }
        }
        blockers.extend(self.deferred_control_blockers(&sites));
        if let SolveResult::Incomplete { blockers: solver_blockers, .. } = &self.forward {
            for blocker in solver_blockers {
                match blocker {
                    Blocker::PendingNode(node) if self.can_reach_any(*node, &sites) => {
                        blockers.insert(FactBlocker::Budget(*node));
                    }
                    Blocker::PendingNode(_) => {}
                    Blocker::OpaqueNode { node, reason }
                        if self.can_reach_any(*node, &sites)
                            && uses.iter().any(|path| self.opaque_relevant(*node, path)) =>
                    {
                        blockers.insert(FactBlocker::OpaqueNode(*node, reason.clone()));
                    }
                    Blocker::OpaqueNode { .. } => {}
                    Blocker::OpaqueEdge { edge, reason } => {
                        if self
                            .cfg
                            .edge(*edge)
                            .map_or(true, |item| self.can_reach_any(item.target, &sites))
                        {
                            blockers.insert(FactBlocker::OpaqueEdge(*edge, reason.clone()));
                        }
                    }
                }
            }
        }
        blockers
    }

    fn variable_assignment_sites(
        &self,
        variable: parser::hir::SymbolId,
        sites: &mut BTreeSet<NodeId>,
        seen: &mut BTreeSet<parser::hir::SymbolId>,
    ) {
        if !seen.insert(variable) {
            return;
        }
        for id in self.cfg.nodes() {
            let Some(CfgNodeKind::Assignment { target, value }) =
                self.cfg.node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            if target.root != variable {
                continue;
            }
            sites.insert(*id);
            let mut nested = BTreeSet::new();
            value.visit_accesses(self.hir, &mut |path| {
                if self
                    .hir
                    .symbol(path.root)
                    .is_some_and(|symbol| symbol.kind == parser::hir::SymbolKind::Variable)
                {
                    nested.insert(path.root);
                }
            });
            for child in nested {
                self.variable_assignment_sites(child, sites, seen);
            }
        }
    }

    fn scalar_blockers(&self, expression: ExprId) -> BTreeSet<FactBlocker> {
        let mut blockers = BTreeSet::new();
        let Some(expr) = self.hir.expression(expression) else {
            blockers.insert(FactBlocker::OpaqueExpression(expression));
            return blockers;
        };
        if let ExprKind::Array(_) | ExprKind::Tuple(_) = &expr.kind {
            blockers.insert(FactBlocker::AggregateAccess);
        }
        expression.visit_accesses(self.hir, &mut |path| {
            let index_count = path
                .steps
                .iter()
                .filter(|step| matches!(step, parser::hir::AccessStep::Index { .. }))
                .count();
            if self.hir.symbol(path.terminal).is_some_and(|symbol| {
                symbol.rank > index_count || symbol.kind == parser::hir::SymbolKind::Bus
            }) {
                blockers.insert(FactBlocker::AggregateAccess);
            }
        });
        blockers
    }

    fn degree_of(&self, expression: ExprId) -> DegreeUpper {
        use parser::new_frontend::BinaryOperator;
        let Some(expr) = self.hir.expression(expression) else { return DegreeUpper::Unbounded };
        match &expr.kind {
            ExprKind::Number(_) => DegreeUpper::Constant,
            ExprKind::Access(path) => match self.hir.symbol(path.root).map(|symbol| symbol.kind) {
                Some(parser::hir::SymbolKind::Parameter | parser::hir::SymbolKind::Tag) => {
                    DegreeUpper::Constant
                }
                Some(parser::hir::SymbolKind::Signal | parser::hir::SymbolKind::Bus) => {
                    DegreeUpper::Linear
                }
                _ => DegreeUpper::Unbounded,
            },
            ExprKind::Unary { operator: parser::new_frontend::UnaryOperator::Negate, operand }
            | ExprKind::Parallel(operand) => self.degree_of(*operand),
            ExprKind::Unary { .. } => DegreeUpper::Unbounded,
            ExprKind::Binary { operator, left, right } => {
                let left = self.degree_of(*left);
                let right = self.degree_of(*right);
                match operator {
                    BinaryOperator::Add | BinaryOperator::Subtract => left.max(right),
                    BinaryOperator::Multiply => left.multiply(right),
                    _ => DegreeUpper::Unbounded,
                }
            }
            ExprKind::Ternary { condition, yes, no } => {
                let empty = BTreeMap::new();
                let Some(condition) =
                    forward::eval_expression(self.hir, self.field, *condition, &empty)
                else {
                    return DegreeUpper::Unbounded;
                };
                if self.field.is_zero(&condition) {
                    self.degree_of(*no)
                } else {
                    self.degree_of(*yes)
                }
            }
            ExprKind::Call { .. }
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Array(_)
            | ExprKind::Tuple(_)
            | ExprKind::Opaque(_) => DegreeUpper::Unbounded,
        }
    }
    /// May-liveness immediately before a CFG node.
    pub fn live_before(&self, node: NodeId, path: &AccessPath) -> Fact<bool> {
        let blockers = self.backward_blockers(path);
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        let facts = match &self.backward {
            SolveResult::Complete(facts) => facts.get(&node),
            SolveResult::Incomplete { provisional_facts, .. } => provisional_facts.get(&node),
        };
        let Some(state) = facts.and_then(|facts| facts.input.as_ref()) else {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        };
        let key = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        Fact::known(state.contains_alias(&key).unwrap_or(false))
    }

    fn backward_blockers(&self, path: &AccessPath) -> BTreeSet<FactBlocker> {
        let mut blockers = self.blockers_for(path);
        let SolveResult::Incomplete { blockers: backward, .. } = &self.backward else {
            return blockers;
        };
        for blocker in backward {
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

    /// Whether a local access can occur in a generated constraint.
    pub fn incidence(&self, path: &AccessPath) -> Fact<Incidence> {
        let blockers = self.blockers_for(path);
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        let query = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        if self.potential_sites(&query).is_empty() {
            return Fact::known(Incidence::Zero);
        }
        let Some(state) = self.exit_state() else {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        };
        let Some((may, must)) = state.constraints() else {
            return Fact::known(Incidence::Zero);
        };
        let must_match = must.iter().any(|site| self.site_touches(*site, &query, true));
        let may_match = may.iter().any(|site| self.site_touches(*site, &query, false));
        let value = if must_match {
            Incidence::Must
        } else if may_match {
            Incidence::May
        } else {
            Incidence::Zero
        };
        Fact::known(value)
    }

    /// An exact value proved by a generated equality on every reachable path.
    pub fn constraint_fixed(&self, path: &AccessPath) -> Fact<Option<FieldValue>> {
        let blockers = self.blockers_for(path);
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        let query = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        if self.potential_sites(&query).is_empty() {
            return Fact::known(None);
        }
        let Some(state) = self.exit_state() else {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        };
        let Some((_, must)) = state.constraints() else {
            return Fact::known(None);
        };
        let values: BTreeSet<_> =
            must.iter().filter_map(|site| self.site_fixed_value(*site, &query)).collect();
        Fact::known((values.len() == 1).then(|| values.into_iter().next()).flatten())
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
        let variables = self.site_state(id).and_then(ForwardState::variables);
        let empty = BTreeMap::new();
        let variables = variables.unwrap_or(&empty);
        self.site_touches_with_variables(id, query, exact, variables)
    }

    fn site_touches_with_variables(
        &self,
        id: NodeId,
        query: &AccessKey,
        exact: bool,
        variables: &BTreeMap<parser::hir::SymbolId, FieldValue>,
    ) -> bool {
        let Some(node) = self.cfg.node(id) else { return true };
        let CfgNodeKind::Constraint { target, left, right } = &node.kind else { return false };
        let target_touches = target.as_ref().is_some_and(|path| {
            let key = key_for_path(self.hir, self.field, path, variables);
            if exact {
                key.exact_alias(query)
            } else {
                key.may_alias(query)
            }
        });
        let index_touches = target.as_ref().is_some_and(|path| {
            !exact
                && path.steps.iter().any(|step| match step {
                    parser::hir::AccessStep::Index {
                        index: parser::hir::ArrayIndex::Symbolic(id),
                        ..
                    } => self.expr_touches(*id, query, variables, false),
                    parser::hir::AccessStep::Index {
                        index: parser::hir::ArrayIndex::Constant(_),
                        ..
                    }
                    | parser::hir::AccessStep::Port { .. }
                    | parser::hir::AccessStep::Tag { .. } => false,
                })
        });
        target_touches
            || index_touches
            || self.expr_touches(*left, query, variables, exact)
            || right.is_some_and(|id| self.expr_touches(id, query, variables, exact))
    }

    fn expr_touches(
        &self,
        id: ExprId,
        query: &AccessKey,
        variables: &BTreeMap<parser::hir::SymbolId, FieldValue>,
        exact: bool,
    ) -> bool {
        let mut found = false;
        let mut variable_uses = BTreeSet::new();
        let complete = id.visit_accesses(self.hir, &mut |path| {
            let key = key_for_path(self.hir, self.field, path, variables);
            found |= if exact { key.exact_alias(query) } else { key.may_alias(query) };
            if !exact
                && self
                    .hir
                    .symbol(path.root)
                    .is_some_and(|symbol| symbol.kind == parser::hir::SymbolKind::Variable)
            {
                variable_uses.insert(path.root);
            }
        });
        if !exact {
            let mut seen = BTreeSet::new();
            for variable in variable_uses {
                found |= self.variable_reaches(variable, query, variables, &mut seen);
            }
        }
        found || (!complete && !exact)
    }

    fn variable_reaches(
        &self,
        variable: parser::hir::SymbolId,
        query: &AccessKey,
        variables: &BTreeMap<parser::hir::SymbolId, FieldValue>,
        seen: &mut BTreeSet<parser::hir::SymbolId>,
    ) -> bool {
        if !seen.insert(variable) {
            return false;
        }
        for node in self.cfg.nodes() {
            let Some(CfgNodeKind::Assignment { target, value }) =
                self.cfg.node(*node).map(|item| &item.kind)
            else {
                continue;
            };
            if target.root != variable {
                continue;
            }
            let mut reached = false;
            let mut nested = BTreeSet::new();
            let complete = value.visit_accesses(self.hir, &mut |path| {
                let key = key_for_path(self.hir, self.field, path, variables);
                reached |= key.may_alias(query);
                if self
                    .hir
                    .symbol(path.root)
                    .is_some_and(|symbol| symbol.kind == parser::hir::SymbolKind::Variable)
                {
                    nested.insert(path.root);
                }
            });
            if reached || !complete {
                return true;
            }
            for child in nested {
                if self.variable_reaches(child, query, variables, seen) {
                    return true;
                }
            }
        }
        false
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
        let query = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        let potential_sites = self.potential_sites(&query);
        blockers.extend(self.deferred_control_blockers(&potential_sites));
        if self.hir.components().iter().any(|item| item.symbol == path.root) {
            blockers.insert(FactBlocker::ExternalSummary);
        }
        if self.hir.symbol(path.terminal).is_some_and(|symbol| {
            symbol.rank
                > path
                    .steps
                    .iter()
                    .filter(|step| matches!(step, parser::hir::AccessStep::Index { .. }))
                    .count()
                || symbol.kind == parser::hir::SymbolKind::Bus
        }) {
            blockers.insert(FactBlocker::AggregateAccess);
        }
        if let Some(state) = self.exit_state() {
            if let Some((may, _)) = state.constraints() {
                for site in may {
                    if self.aggregate_site_touches(*site, &query) {
                        blockers.insert(FactBlocker::AggregateConstraint(*site));
                    }
                }
            }
        }
        let SolveResult::Incomplete { blockers: solver_blockers, .. } = &self.forward else {
            return blockers;
        };
        for blocker in solver_blockers {
            match blocker {
                Blocker::PendingNode(node)
                    if self.can_reach_any(*node, &potential_sites)
                        || self.opaque_relevant(*node, path) && self.is_opaque_node(*node) =>
                {
                    blockers.insert(FactBlocker::Budget(*node));
                }
                Blocker::PendingNode(_) => {}
                Blocker::OpaqueEdge { edge, reason } => {
                    if self
                        .cfg
                        .edge(*edge)
                        .map_or(true, |item| self.can_reach_any(item.target, &potential_sites))
                    {
                        blockers.insert(FactBlocker::OpaqueEdge(*edge, reason.clone()));
                    }
                }
                Blocker::OpaqueNode { node, reason } if self.opaque_relevant(*node, path) => {
                    blockers.insert(FactBlocker::OpaqueNode(*node, reason.clone()));
                }
                Blocker::OpaqueNode { .. } => {}
            }
        }
        blockers
    }

    fn potential_sites(&self, query: &AccessKey) -> BTreeSet<NodeId> {
        let empty = BTreeMap::new();
        self.cfg
            .nodes()
            .iter()
            .copied()
            .filter(|node| self.site_touches_with_variables(*node, query, false, &empty))
            .collect()
    }

    fn can_reach_any(&self, start: NodeId, targets: &BTreeSet<NodeId>) -> bool {
        let mut visited = BTreeSet::new();
        let mut queue = vec![start];
        while let Some(node) = queue.pop() {
            if !visited.insert(node) {
                continue;
            }
            if targets.contains(&node) {
                return true;
            }
            for edge in self.cfg.edges() {
                if let Some(item) = self.cfg.edge(*edge) {
                    if item.source == node {
                        queue.push(item.target);
                    }
                }
            }
        }
        false
    }

    fn deferred_control_blockers(&self, sites: &BTreeSet<NodeId>) -> BTreeSet<FactBlocker> {
        let mut blockers = BTreeSet::new();
        for id in self.cfg.nodes() {
            let Some(CfgNodeKind::Branch {
                guard: parser::hir::ControlGuard::DeferredScalar, ..
            }) = self.cfg.node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            let mut true_target = None;
            let mut false_target = None;
            for edge_id in self.cfg.edges() {
                let Some(edge) = self.cfg.edge(*edge_id) else { continue };
                if edge.source != *id {
                    continue;
                }
                match edge.payload.kind {
                    crate::hir_cfg::EdgeKind::True => true_target = Some(edge.target),
                    crate::hir_cfg::EdgeKind::False => false_target = Some(edge.target),
                    crate::hir_cfg::EdgeKind::Normal
                    | crate::hir_cfg::EdgeKind::Loop
                    | crate::hir_cfg::EdgeKind::Return => {}
                }
            }
            let (Some(yes), Some(no)) = (true_target, false_target) else { continue };
            for site in sites {
                let target = BTreeSet::from([*site]);
                if self.can_reach_any(yes, &target) != self.can_reach_any(no, &target) {
                    blockers.insert(FactBlocker::DeferredControl(*id));
                }
            }
        }
        blockers
    }

    fn is_opaque_node(&self, id: NodeId) -> bool {
        let Some(node) = self.cfg.node(id) else { return true };
        match &node.kind {
            CfgNodeKind::Opaque(_) | CfgNodeKind::Instantiate { .. } => true,
            CfgNodeKind::Evaluate(expr) => {
                self.hir.expression(*expr).map_or(true, |item| match &item.kind {
                    ExprKind::Opaque(_) | ExprKind::AnonymousComponent { .. } => true,
                    ExprKind::Number(_)
                    | ExprKind::Access(_)
                    | ExprKind::Call { .. }
                    | ExprKind::Array(_)
                    | ExprKind::Tuple(_)
                    | ExprKind::Unary { .. }
                    | ExprKind::Binary { .. }
                    | ExprKind::Ternary { .. }
                    | ExprKind::Parallel(_) => false,
                })
            }
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::LoopHeader
            | CfgNodeKind::Branch { .. }
            | CfgNodeKind::Witness { .. }
            | CfgNodeKind::Constraint { .. }
            | CfgNodeKind::Assignment { .. }
            | CfgNodeKind::Update { .. }
            | CfgNodeKind::Declaration
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Assert { .. }
            | CfgNodeKind::Log => false,
        }
    }

    fn aggregate_site_touches(&self, site: NodeId, query: &AccessKey) -> bool {
        let Some(node) = self.cfg.node(site) else { return true };
        let CfgNodeKind::Constraint { target, left, right } = &node.kind else { return false };
        let empty = BTreeMap::new();
        let variables = self.site_state(site).and_then(ForwardState::variables).unwrap_or(&empty);
        let aggregate = |path: &AccessPath| {
            let key = key_for_path(self.hir, self.field, path, variables);
            key.steps.len() < query.steps.len() && key.may_alias(query)
        };
        if target.as_ref().is_some_and(&aggregate) {
            return true;
        }
        let mut found = false;
        left.visit_accesses(self.hir, &mut |path| found |= aggregate(path));
        if let Some(right) = right {
            right.visit_accesses(self.hir, &mut |path| found |= aggregate(path));
        }
        found
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
            | parser::hir::Effect::ComponentInstantiation { target, .. } => {
                target.root == path.root
            }
            parser::hir::Effect::ConstraintAssignment { .. }
            | parser::hir::Effect::EqualityConstraint { .. }
            | parser::hir::Effect::VariableAssignment { .. } => true,
            _ => true,
        }
    }
}
