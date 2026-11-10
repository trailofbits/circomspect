//! Immutable control flow graphs over the checked HIR.

mod index;

#[cfg(test)]
pub(crate) mod component_fixture;

use std::collections::{BTreeMap, BTreeSet};

use crate::hir_cfg::index::TopologyIndex;

use abstract_interpretation::graph::{EdgeId, EdgeRef, FlowGraph, GraphError, IndexedGraph, NodeId};
use num_traits::ToPrimitive;
use parser::hir::{
    AccessPath, AccessStep, ArrayIndex, BlockId, ControlGuard, DefinitionRef, Effect, ExprId,
    ExprKind, HirProject, IncompleteReason, PortSchema, SymbolId, SymbolKind, ValueEvidence,
};
use parser::frontend::{AssignmentOperator, BinaryOperator, PostfixOperator, Span};

use crate::scalar_evidence::ScalarExpressionEvidence;
use crate::hir_facts::FieldValue;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Origin {
    pub block: BlockId,
    pub effect_index: usize,
    pub expression: Option<ExprId>,
    pub span: Span,
}

/// A constraint with an explicit assignment target or two equality operands.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Constraint {
    Assignment { target: AccessPath, value: ExprId },
    Equality { left: ExprId, right: ExprId },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CfgNodeKind {
    Entry,
    Exit,
    Evaluate(ExprId),
    LoopHeader,
    Branch {
        condition: ExprId,
        guard: ControlGuard,
    },
    Witness {
        target: AccessPath,
        value: ExprId,
    },
    Constraint(Constraint),
    Assignment {
        target: AccessPath,
        value: ExprId,
        operator: AssignmentOperator,
    },
    DeferredAssignment {
        target: AccessPath,
        value: ExprId,
        operator: AssignmentOperator,
    },
    Update {
        target: AccessPath,
        operator: PostfixOperator,
    },
    Instantiate {
        target: AccessPath,
        value: ExprId,
    },
    OpaqueAssignment {
        target: AccessPath,
        value: ExprId,
        operator: AssignmentOperator,
        reason: IncompleteReason,
    },
    OpaqueEquality {
        left: ExprId,
        right: ExprId,
        reason: IncompleteReason,
    },
    Declaration {
        symbol: SymbolId,
    },
    Return(ExprId),
    Assert {
        condition: ExprId,
    },
    DeferredAssert {
        condition: ExprId,
    },
    Log,
    Opaque(IncompleteReason),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CfgNode {
    pub id: NodeId,
    pub kind: CfgNodeKind,
    pub origin: Option<Origin>,
    pub deferred_controls: BTreeSet<NodeId>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EdgeKind {
    Normal,
    True,
    False,
    Loop,
    Return,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CfgEdge {
    pub id: EdgeId,
    pub kind: EdgeKind,
    pub condition: Option<ExprId>,
    pub guard: Option<ControlGuard>,
}

/// A graph bound to the definition from which it was built.
///
/// ```compile_fail
/// use circomspect_program_analysis::hir_cfg::DefinitionCfg;
/// use parser::hir::DefinitionRef;
/// fn forge(mut cfg: DefinitionCfg, value: DefinitionRef) { cfg.definition = value; }
/// ```
/// ```compile_fail
/// use circomspect_program_analysis::hir_cfg::DefinitionCfg;
/// use abstract_interpretation::graph::NodeId;
/// fn forge(mut cfg: DefinitionCfg, value: NodeId) { cfg.entry = value; }
/// ```
/// ```compile_fail
/// use circomspect_program_analysis::hir_cfg::DefinitionCfg;
/// use abstract_interpretation::graph::NodeId;
/// fn forge(mut cfg: DefinitionCfg, value: NodeId) { cfg.exit = value; }
/// ```
#[derive(Clone)]
pub struct DefinitionCfg {
    graph: IndexedGraph<CfgNode, CfgEdge>,
    topology: TopologyIndex,
    evaluations: BTreeMap<ExprId, Vec<NodeId>>,
    local_symbols: BTreeSet<SymbolId>,
    checked_paths: Vec<AccessPath>,
    scalar_seeds: Option<BTreeMap<SymbolId, FieldValue>>,
    definition: DefinitionRef,
    entry: NodeId,
    exit: NodeId,
}

impl DefinitionCfg {
    #[must_use]
    pub fn definition(&self) -> DefinitionRef {
        self.definition
    }

    #[must_use]
    pub fn entry(&self) -> NodeId {
        self.entry
    }

    #[must_use]
    pub fn exit(&self) -> NodeId {
        self.exit
    }

    pub(crate) fn evaluation_sites(&self, expression: ExprId) -> &[NodeId] {
        self.evaluations.get(&expression).map_or(&[], Vec::as_slice)
    }

    pub(crate) fn evaluated_expressions(&self) -> impl Iterator<Item = ExprId> + '_ {
        self.evaluations.keys().copied()
    }

    pub(crate) fn path_exists(
        &self,
        start: NodeId,
        targets: &BTreeSet<NodeId>,
        excluded: Option<NodeId>,
        pruned: &BTreeSet<EdgeId>,
    ) -> bool {
        self.topology.reaches(start, targets, excluded, pruned)
    }

    /// Nodes with a path to any target, including the targets themselves.
    pub(crate) fn nodes_reaching(&self, targets: &BTreeSet<NodeId>) -> BTreeSet<NodeId> {
        self.topology.nodes_reaching(targets)
    }

    /// Unpruned reachable nodes, including `start`, or `None` when capacity is exceeded.
    pub(crate) fn reachable_nodes(
        &self,
        start: NodeId,
        capacity: usize,
    ) -> Option<BTreeSet<NodeId>> {
        self.topology.reachable_nodes(start, capacity)
    }

    pub(crate) fn owns_symbol(&self, symbol: SymbolId) -> bool {
        self.local_symbols.contains(&symbol)
    }

    pub(crate) fn scalar_seeds(&self) -> Option<&BTreeMap<SymbolId, FieldValue>> {
        self.scalar_seeds.as_ref()
    }

    pub(crate) fn owns_path(&self, path: &AccessPath) -> bool {
        if !self.owns_symbol(path.root) {
            return false;
        }
        if path.steps.is_empty() {
            return true;
        }
        self.checked_paths.iter().any(|checked| {
            checked.root == path.root
                && checked.terminal == path.terminal
                && checked.steps.len() == path.steps.len()
                && checked.steps.iter().zip(&path.steps).all(|(left, right)| match (left, right) {
                    (
                        AccessStep::Index { index: left, .. },
                        AccessStep::Index { index: right, .. },
                    ) => left == right,
                    (AccessStep::Port { port: left, .. }, AccessStep::Port { port: right, .. }) => {
                        left == right
                    }
                    (
                        AccessStep::Tag { symbol: left, .. },
                        AccessStep::Tag { symbol: right, .. },
                    ) => left == right,
                    _ => false,
                })
        })
    }
}

impl FlowGraph for DefinitionCfg {
    type NodeId = NodeId;
    type EdgeId = EdgeId;
    type Node = CfgNode;
    type Edge = CfgEdge;

    fn nodes(&self) -> &[NodeId] {
        self.graph.nodes()
    }
    fn edges(&self) -> &[EdgeId] {
        self.graph.edges()
    }
    fn node(&self, id: NodeId) -> Option<&CfgNode> {
        self.graph.node(id)
    }
    fn edge(&self, id: EdgeId) -> Option<EdgeRef<'_, NodeId, CfgEdge>> {
        self.graph.edge(id)
    }
    fn entries(&self) -> &[NodeId] {
        self.graph.entries()
    }
    fn exits(&self) -> &[NodeId] {
        self.graph.exits()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BuildError {
    ForeignDefinition,
    ForeignCallResults,
    ForeignScalarSeeds,
    MissingBlock(BlockId),
    MissingExpression(ExprId),
    MissingSymbol(SymbolId),
    MissingPort(parser::hir::PortId),
    UnexpectedEffect,
    InvalidLoopPlan,
    InvalidGraph(GraphError<NodeId, EdgeId>),
}

type Tails = Vec<(NodeId, EdgeKind)>;

#[derive(Clone, Copy)]
struct LoopPlan {
    condition: ExprId,
    guard: ControlGuard,
    body: BlockId,
    step: Option<BlockId>,
    origin: Origin,
}

#[derive(Clone, Copy)]
enum AssignmentKind<'a> {
    Variable(AssignmentOperator),
    Deferred(AssignmentOperator),
    Component,
    Witness,
    Constraint,
    Opaque { operator: AssignmentOperator, reason: &'a IncompleteReason },
}

enum SpecializedAssignment {
    Variable,
    Witness,
    Constraint,
}

struct TernaryExpression {
    expression: ExprId,
    condition: ExprId,
    yes: ExprId,
    no: ExprId,
}

enum EvaluationFrame {
    Visit(ExprId),
    Emit(ExprId),
    Branch(TernaryExpression),
    Else { expression: ExprId, branch: NodeId, no: ExprId, control: Option<NodeId> },
    Join { expression: ExprId, yes_tails: Tails, control: Option<NodeId> },
}

fn push_expressions(
    frames: &mut Vec<EvaluationFrame>,
    expressions: impl DoubleEndedIterator<Item = ExprId>,
) {
    for expression in expressions.rev() {
        frames.push(EvaluationFrame::Visit(expression));
    }
}

struct Builder<'a> {
    hir: &'a HirProject,
    calls: Option<&'a ScalarExpressionEvidence>,
    scalar_seeds: Option<&'a BTreeMap<SymbolId, FieldValue>>,
    nodes: Vec<CfgNode>,
    edges: Vec<(NodeId, NodeId, CfgEdge)>,
    conditions: BTreeMap<NodeId, (ExprId, ControlGuard)>,
    active_deferred: Vec<NodeId>,
    local_symbols: BTreeSet<SymbolId>,
    checked_paths: Vec<AccessPath>,
    exit: NodeId,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum ScalarShapeProof {
    Checked,
    Seeded,
}

impl Builder<'_> {
    fn node(&mut self, kind: CfgNodeKind, origin: Option<Origin>) -> NodeId {
        let id = NodeId::new(self.nodes.len());
        if let CfgNodeKind::Branch { condition, guard } = &kind {
            self.conditions.insert(id, (*condition, *guard));
        }
        let deferred_controls = self.active_deferred.iter().copied().collect();
        self.nodes.push(CfgNode { id, kind, origin, deferred_controls });
        id
    }

    fn link(&mut self, tails: Tails, node: NodeId) {
        for (source, kind) in tails {
            let (condition, guard) = self
                .conditions
                .get(&source)
                .map_or((None, None), |(condition, guard)| (Some(*condition), Some(*guard)));
            let id = EdgeId::new(self.edges.len());
            self.edges.push((source, node, CfgEdge { id, kind, condition, guard }));
        }
    }

    fn append(&mut self, tails: Tails, kind: CfgNodeKind, origin: Origin) -> Tails {
        let id = self.node(kind, Some(origin));
        self.link(tails, id);
        vec![(id, EdgeKind::Normal)]
    }

    fn evaluate(
        &mut self,
        mut tails: Tails,
        id: ExprId,
        origin: Origin,
    ) -> Result<Tails, BuildError> {
        let mut frames = vec![EvaluationFrame::Visit(id)];
        while let Some(frame) = frames.pop() {
            match frame {
                EvaluationFrame::Visit(expression) => {
                    self.schedule_expression(expression, &mut frames)?;
                }
                EvaluationFrame::Emit(expression) => {
                    tails = self.emit_expression(tails, expression, origin)?;
                }
                EvaluationFrame::Branch(ternary) => {
                    tails = self.begin_expression_branch(tails, &ternary, &mut frames, origin)?;
                }
                EvaluationFrame::Else { expression, branch, no, control } => {
                    frames.push(EvaluationFrame::Join { expression, yes_tails: tails, control });
                    frames.push(EvaluationFrame::Visit(no));
                    tails = vec![(branch, EdgeKind::False)];
                }
                EvaluationFrame::Join { expression, mut yes_tails, control } => {
                    yes_tails.append(&mut tails);
                    tails = self.emit_expression(yes_tails, expression, origin)?;
                    if let Some(control) = control {
                        if self.active_deferred.pop() != Some(control) {
                            return Err(BuildError::UnexpectedEffect);
                        }
                    }
                }
            }
        }
        Ok(tails)
    }

    fn emit_expression(
        &mut self,
        tails: Tails,
        expression: ExprId,
        origin: Origin,
    ) -> Result<Tails, BuildError> {
        let origin = self.expression_origin(expression, origin)?;
        Ok(self.append(tails, CfgNodeKind::Evaluate(expression), origin))
    }

    fn schedule_expression(
        &mut self,
        expression: ExprId,
        frames: &mut Vec<EvaluationFrame>,
    ) -> Result<(), BuildError> {
        let expr =
            self.hir.expression(expression).ok_or(BuildError::MissingExpression(expression))?;
        if let ExprKind::Ternary { condition, yes, no } = &expr.kind {
            frames.push(EvaluationFrame::Branch(TernaryExpression {
                expression,
                condition: *condition,
                yes: *yes,
                no: *no,
            }));
            frames.push(EvaluationFrame::Visit(*condition));
            return Ok(());
        }
        frames.push(EvaluationFrame::Emit(expression));
        self.schedule_operands(expression, frames)
    }

    fn schedule_operands(
        &mut self,
        expression: ExprId,
        frames: &mut Vec<EvaluationFrame>,
    ) -> Result<(), BuildError> {
        let expr =
            self.hir.expression(expression).ok_or(BuildError::MissingExpression(expression))?;
        match &expr.kind {
            ExprKind::Number(_) | ExprKind::Opaque(_) => {}
            ExprKind::Access(path) => {
                self.checked_paths.push(path.clone());
                Self::schedule_access_indices(path, frames);
            }
            ExprKind::Call { arguments, .. } => {
                push_expressions(frames, arguments.iter().copied());
            }
            ExprKind::AnonymousComponent { arguments, inputs, .. } => {
                push_expressions(frames, inputs.iter().map(|input| input.value));
                push_expressions(frames, arguments.iter().copied());
            }
            ExprKind::Array(values) | ExprKind::Tuple(values) => {
                push_expressions(frames, values.iter().copied());
            }
            ExprKind::Unary { operand, .. } | ExprKind::Parallel(operand) => {
                frames.push(EvaluationFrame::Visit(*operand));
            }
            ExprKind::Binary { left, right, .. } => {
                frames.push(EvaluationFrame::Visit(*right));
                frames.push(EvaluationFrame::Visit(*left));
            }
            ExprKind::Ternary { .. } => return Err(BuildError::UnexpectedEffect),
        }
        Ok(())
    }

    fn schedule_access_indices(path: &AccessPath, frames: &mut Vec<EvaluationFrame>) {
        for step in path.steps.iter().rev() {
            if let AccessStep::Index { index: parser::hir::ArrayIndex::Symbolic(index), .. } = step
            {
                frames.push(EvaluationFrame::Visit(*index));
            }
        }
    }

    fn begin_expression_branch(
        &mut self,
        tails: Tails,
        ternary: &TernaryExpression,
        frames: &mut Vec<EvaluationFrame>,
        origin: Origin,
    ) -> Result<Tails, BuildError> {
        let expr = self
            .hir
            .expression(ternary.expression)
            .ok_or(BuildError::MissingExpression(ternary.expression))?;
        let guard = if expr.knownness == parser::hir::Knownness::Constant {
            ControlGuard::CheckedCompileTime
        } else {
            ControlGuard::DeferredScalar
        };
        let branch_origin = self.expression_origin(ternary.condition, origin)?;
        let branch = self
            .node(CfgNodeKind::Branch { condition: ternary.condition, guard }, Some(branch_origin));
        self.link(tails, branch);
        let control = if guard == ControlGuard::DeferredScalar {
            self.active_deferred.push(branch);
            Some(branch)
        } else {
            None
        };
        frames.push(EvaluationFrame::Else {
            expression: ternary.expression,
            branch,
            no: ternary.no,
            control,
        });
        frames.push(EvaluationFrame::Visit(ternary.yes));
        Ok(vec![(branch, EdgeKind::True)])
    }

    fn block(&mut self, mut tails: Tails, id: BlockId) -> Result<Tails, BuildError> {
        let block = self.hir.block(id).ok_or(BuildError::MissingBlock(id))?;
        for (effect_index, effect) in block.effects.iter().enumerate() {
            if tails.is_empty() {
                break;
            }
            let origin = Origin {
                block: id,
                effect_index,
                expression: None,
                span: effect_span(effect, block.span),
            };
            tails = self.effect(tails, effect, origin)?;
        }
        Ok(tails)
    }

    fn effect(
        &mut self,
        tails: Tails,
        effect: &Effect,
        origin: Origin,
    ) -> Result<Tails, BuildError> {
        match effect {
            Effect::Declaration { symbol, .. } => self.declaration_effect(tails, *symbol, origin),
            Effect::VariableAssignment { target, value, operator, .. } => self.assignment_effect(
                tails,
                target,
                *value,
                AssignmentKind::Variable(*operator),
                origin,
            ),
            Effect::DeferredVariableAssignment { target, value, operator, .. } => self
                .assignment_effect(
                    tails,
                    target,
                    *value,
                    AssignmentKind::Deferred(*operator),
                    origin,
                ),
            Effect::ComponentInstantiation { target, value, .. } => {
                self.assignment_effect(tails, target, *value, AssignmentKind::Component, origin)
            }
            Effect::WitnessAssignment { target, value, .. } => {
                self.assignment_effect(tails, target, *value, AssignmentKind::Witness, origin)
            }
            Effect::ConstraintAssignment { target, value, .. } => {
                self.assignment_effect(tails, target, *value, AssignmentKind::Constraint, origin)
            }
            Effect::OpaqueAssignment { target, value, operator, reason, .. } => self
                .assignment_effect(
                    tails,
                    target,
                    *value,
                    AssignmentKind::Opaque { operator: *operator, reason },
                    origin,
                ),
            Effect::EqualityConstraint { left, right, .. } => {
                self.equality_effect(tails, *left, *right, None, origin)
            }
            Effect::OpaqueEquality { left, right, reason, .. } => {
                self.equality_effect(tails, *left, *right, Some(reason), origin)
            }
            Effect::Update { target, operator, .. } => {
                let tails = self.evaluate_target(tails, target, origin)?;
                Ok(self.append(
                    tails,
                    CfgNodeKind::Update { target: target.clone(), operator: *operator },
                    origin,
                ))
            }
            Effect::If { .. } => self.if_effect(tails, effect, origin),
            Effect::While { condition, guard, body, .. } => self.loop_effect(
                tails,
                LoopPlan { condition: *condition, guard: *guard, body: *body, step: None, origin },
            ),
            Effect::For { .. } => self.for_effect(tails, effect, origin),
            Effect::Return { value, .. } => {
                let tails = self.evaluate(tails, *value, origin)?;
                let tails = self.append(tails, CfgNodeKind::Return(*value), origin);
                self.link(
                    tails.into_iter().map(|(id, _)| (id, EdgeKind::Return)).collect(),
                    self.exit,
                );
                Ok(Vec::new())
            }
            Effect::Assert { condition, .. } => {
                let tails = self.evaluate(tails, *condition, origin)?;
                Ok(self.append(tails, CfgNodeKind::Assert { condition: *condition }, origin))
            }
            Effect::DeferredAssert { condition, .. } => {
                let tails = self.evaluate(tails, *condition, origin)?;
                Ok(self.append(
                    tails,
                    CfgNodeKind::DeferredAssert { condition: *condition },
                    origin,
                ))
            }
            Effect::Log { values, .. } => {
                let mut tails = tails;
                for &value in values {
                    tails = self.evaluate(tails, value, origin)?;
                }
                Ok(self.append(tails, CfgNodeKind::Log, origin))
            }
            Effect::AnonymousComponent { expression, .. } => {
                self.evaluate(tails, *expression, origin)
            }
            Effect::Block(block) => self.block(tails, *block),
            Effect::Opaque { reason, .. } => {
                Ok(self.append(tails, CfgNodeKind::Opaque(reason.clone()), origin))
            }
        }
    }

    fn declaration_effect(
        &mut self,
        tails: Tails,
        symbol: SymbolId,
        origin: Origin,
    ) -> Result<Tails, BuildError> {
        let declared = self.hir.symbol(symbol).ok_or(BuildError::MissingSymbol(symbol))?;
        self.local_symbols.insert(symbol);
        let mut tails = tails;
        for &dimension in &declared.dimensions {
            tails = self.evaluate(tails, dimension, origin)?;
        }
        Ok(self.append(tails, CfgNodeKind::Declaration { symbol }, origin))
    }

    fn assignment_effect(
        &mut self,
        tails: Tails,
        target: &AccessPath,
        value: ExprId,
        kind: AssignmentKind<'_>,
        origin: Origin,
    ) -> Result<Tails, BuildError> {
        let tails = self.evaluate_target(tails, target, origin)?;
        let tails = self.evaluate(tails, value, origin)?;
        let effect_origin = Origin { expression: Some(value), ..origin };
        let node = match kind {
            AssignmentKind::Variable(operator) => {
                CfgNodeKind::Assignment { target: target.clone(), value, operator }
            }
            AssignmentKind::Deferred(operator) => {
                return Ok(self.append(
                    tails,
                    CfgNodeKind::DeferredAssignment { target: target.clone(), value, operator },
                    origin,
                ));
            }
            AssignmentKind::Component => CfgNodeKind::Instantiate { target: target.clone(), value },
            AssignmentKind::Witness => CfgNodeKind::Witness { target: target.clone(), value },
            AssignmentKind::Constraint => {
                return Ok(self.append_constraint_assignment(tails, target, value, effect_origin));
            }
            AssignmentKind::Opaque { operator, reason } => {
                match self.specialized_assignment(target, value, operator, reason) {
                    Some(SpecializedAssignment::Variable) => {
                        CfgNodeKind::Assignment { target: target.clone(), value, operator }
                    }
                    Some(SpecializedAssignment::Witness) => {
                        CfgNodeKind::Witness { target: target.clone(), value }
                    }
                    Some(SpecializedAssignment::Constraint) => {
                        return Ok(self.append_constraint_assignment(
                            tails,
                            target,
                            value,
                            effect_origin,
                        ));
                    }
                    None => CfgNodeKind::OpaqueAssignment {
                        target: target.clone(),
                        value,
                        operator,
                        reason: reason.clone(),
                    },
                }
            }
        };
        Ok(self.append(tails, node, effect_origin))
    }

    fn equality_effect(
        &mut self,
        tails: Tails,
        left: ExprId,
        right: ExprId,
        reason: Option<&IncompleteReason>,
        origin: Origin,
    ) -> Result<Tails, BuildError> {
        let tails = self.evaluate(tails, left, origin)?;
        let tails = self.evaluate(tails, right, origin)?;
        let kind = match reason {
            Some(reason) if !self.specialized_equality(left, right, reason) => {
                CfgNodeKind::OpaqueEquality { left, right, reason: reason.clone() }
            }
            Some(_) | None => CfgNodeKind::Constraint(Constraint::Equality { left, right }),
        };
        Ok(self.append(tails, kind, Origin { expression: Some(left), ..origin }))
    }

    fn append_constraint_assignment(
        &mut self,
        tails: Tails,
        target: &AccessPath,
        value: ExprId,
        origin: Origin,
    ) -> Tails {
        let tails =
            self.append(tails, CfgNodeKind::Witness { target: target.clone(), value }, origin);
        self.append(
            tails,
            CfgNodeKind::Constraint(Constraint::Assignment { target: target.clone(), value }),
            origin,
        )
    }

    fn specialized_assignment(
        &self,
        target: &AccessPath,
        value: ExprId,
        operator: AssignmentOperator,
        reason: &IncompleteReason,
    ) -> Option<SpecializedAssignment> {
        if *reason != IncompleteReason::UnknownType {
            return None;
        }
        let exact_call =
            target.steps.is_empty() && self.calls.and_then(|calls| calls.value(value)).is_some();
        let target_shape = self.scalar_access_proof(target);
        let value_shape = self.scalar_source_shape(value);
        let seeded_scalar = match (target_shape, value_shape) {
            (Some(ScalarShapeProof::Seeded), Some(_))
            | (Some(_), Some(ScalarShapeProof::Seeded)) => true,
            (Some(ScalarShapeProof::Checked), Some(ScalarShapeProof::Checked))
            | (None, _)
            | (_, None) => false,
        };
        if !exact_call && !seeded_scalar {
            return None;
        }
        let symbol = self.hir.symbol(target.terminal)?;
        if symbol.rank != 0 || !symbol.shape_checked {
            return None;
        }
        Self::specialized_kind(symbol.kind, operator)
    }

    fn scalar_source_shape(&self, expression: ExprId) -> Option<ScalarShapeProof> {
        let mut pending = vec![expression];
        let mut proof = ScalarShapeProof::Checked;
        while let Some(id) = pending.pop() {
            let expression = self.hir.expression(id)?;
            match &expression.kind {
                ExprKind::Number(_) => {}
                ExprKind::Access(path) => {
                    if self.scalar_access_shape(path, &mut pending)? == ScalarShapeProof::Seeded {
                        proof = ScalarShapeProof::Seeded;
                    }
                }
                ExprKind::Unary { operand, .. } => pending.push(*operand),
                ExprKind::Binary { left, right, .. } => pending.extend([*left, *right]),
                ExprKind::Call { .. } if self.calls.and_then(|calls| calls.value(id)).is_some() => {
                }
                ExprKind::Call { .. }
                | ExprKind::Array(_)
                | ExprKind::Tuple(_)
                | ExprKind::Ternary { .. }
                | ExprKind::AnonymousComponent { .. }
                | ExprKind::Parallel(_)
                | ExprKind::Opaque(_) => return None,
            }
        }
        Some(proof)
    }

    fn scalar_access_proof(&self, path: &AccessPath) -> Option<ScalarShapeProof> {
        let mut indices = Vec::new();
        let mut proof = self.scalar_access_shape(path, &mut indices)?;
        for index in indices {
            if self.scalar_source_shape(index)? == ScalarShapeProof::Seeded {
                proof = ScalarShapeProof::Seeded;
            }
        }
        Some(proof)
    }

    fn scalar_access_shape(
        &self,
        path: &AccessPath,
        pending: &mut Vec<ExprId>,
    ) -> Option<ScalarShapeProof> {
        let symbol = self.hir.symbol(path.terminal)?;
        if !symbol.shape_checked || symbol.bus_type.is_some() {
            return None;
        }
        if symbol.kind == SymbolKind::Parameter {
            return self.scalar_parameter_shape(path);
        }
        let indices = self.checked_scalar_path_indices(path, pending)?;
        match symbol.kind {
            SymbolKind::Signal if indices == symbol.rank => Some(ScalarShapeProof::Checked),
            SymbolKind::Variable
                if indices == symbol.rank && symbol.value_evidence == ValueEvidence::Checked =>
            {
                Some(ScalarShapeProof::Checked)
            }
            SymbolKind::Parameter
            | SymbolKind::Component
            | SymbolKind::Bus
            | SymbolKind::Tag
            | SymbolKind::Signal
            | SymbolKind::Variable => None,
        }
    }

    fn scalar_parameter_shape(&self, path: &AccessPath) -> Option<ScalarShapeProof> {
        let symbol = self.hir.symbol(path.root)?;
        if path.root != path.terminal
            || !path.steps.is_empty()
            || symbol.rank != 0
            || !self.parameter_is_stable(path.root)
        {
            return None;
        }
        self.scalar_seeds?.get(&path.root)?;
        Some(ScalarShapeProof::Seeded)
    }

    fn checked_scalar_path_indices(
        &self,
        path: &AccessPath,
        pending: &mut Vec<ExprId>,
    ) -> Option<usize> {
        let mut indices = 0;
        for step in &path.steps {
            match step {
                AccessStep::Index { index: ArrayIndex::Constant(_), .. } => indices += 1,
                AccessStep::Index { index: ArrayIndex::Symbolic(id), .. } => {
                    indices += 1;
                    pending.push(*id);
                }
                AccessStep::Port { port, .. } => {
                    let port = self.hir.port(*port)?;
                    if port.schema != PortSchema::Signal || port.symbol != path.terminal {
                        return None;
                    }
                    indices = 0;
                }
                AccessStep::Tag { .. } => return None,
            }
        }
        Some(indices)
    }

    fn specialized_equality(&self, left: ExprId, right: ExprId, reason: &IncompleteReason) -> bool {
        if *reason != IncompleteReason::UnknownType
            || self.calls.and_then(|calls| calls.call_value(right)).is_none()
        {
            return false;
        }
        let Some(ExprKind::Access(path)) = self.hir.expression(left).map(|item| &item.kind) else {
            return false;
        };
        let Some(symbol) = self.hir.symbol(path.terminal) else { return false };
        if path.root != path.terminal
            || symbol.kind != SymbolKind::Signal
            || !symbol.shape_checked
            || symbol.bus_type.is_some()
            || path.steps.len() != symbol.rank
        {
            return false;
        }
        for step in &path.steps {
            if let AccessStep::Index { .. } = step {
                continue;
            }
            return false;
        }
        true
    }

    fn specialized_kind(
        kind: SymbolKind,
        operator: AssignmentOperator,
    ) -> Option<SpecializedAssignment> {
        match kind {
            SymbolKind::Variable => {
                (operator == AssignmentOperator::Assign).then_some(SpecializedAssignment::Variable)
            }
            SymbolKind::Signal => match operator {
                AssignmentOperator::Witness | AssignmentOperator::ReverseWitness => {
                    Some(SpecializedAssignment::Witness)
                }
                AssignmentOperator::Constraint | AssignmentOperator::ReverseConstraint => {
                    Some(SpecializedAssignment::Constraint)
                }
                AssignmentOperator::Assign
                | AssignmentOperator::Add
                | AssignmentOperator::Subtract
                | AssignmentOperator::Multiply
                | AssignmentOperator::Divide
                | AssignmentOperator::IntegerDivide
                | AssignmentOperator::Modulo
                | AssignmentOperator::Power
                | AssignmentOperator::ShiftLeft
                | AssignmentOperator::ShiftRight
                | AssignmentOperator::BitAnd
                | AssignmentOperator::BitOr
                | AssignmentOperator::BitXor => None,
            },
            SymbolKind::Parameter | SymbolKind::Component | SymbolKind::Bus | SymbolKind::Tag => {
                None
            }
        }
    }

    fn if_effect(
        &mut self,
        tails: Tails,
        effect: &Effect,
        origin: Origin,
    ) -> Result<Tails, BuildError> {
        let Effect::If { condition, guard, then_block, else_block, .. } = effect else {
            return Err(BuildError::UnexpectedEffect);
        };
        let tails = self.evaluate(tails, *condition, origin)?;
        let branch_origin = self.expression_origin(*condition, origin)?;
        let branch = self.node(
            CfgNodeKind::Branch { condition: *condition, guard: *guard },
            Some(branch_origin),
        );
        self.link(tails, branch);
        if *guard == ControlGuard::DeferredScalar {
            self.active_deferred.push(branch);
        }
        let then_tails = self.block(vec![(branch, EdgeKind::True)], *then_block)?;
        let else_tails = if let Some(other) = else_block {
            self.block(vec![(branch, EdgeKind::False)], *other)?
        } else {
            vec![(branch, EdgeKind::False)]
        };
        if *guard == ControlGuard::DeferredScalar {
            self.active_deferred.pop();
        }
        Ok([then_tails, else_tails].concat())
    }

    fn for_effect(
        &mut self,
        tails: Tails,
        effect: &Effect,
        origin: Origin,
    ) -> Result<Tails, BuildError> {
        let Effect::For { initializer, condition, step, body, guard, .. } = effect else {
            return Err(BuildError::UnexpectedEffect);
        };
        let iterations = match guard {
            ControlGuard::CheckedCompileTime => {
                self.static_for_iterations(*initializer, *condition, *step, *body)
            }
            ControlGuard::DeferredScalar if self.scalar_seeds.is_some() => {
                self.static_for_iterations(*initializer, *condition, *step, *body)
            }
            ControlGuard::DeferredScalar | ControlGuard::WitnessOnly => None,
        };
        let tails = self.block(tails, *initializer)?;
        let plan = LoopPlan {
            condition: *condition,
            guard: if iterations.is_some() { ControlGuard::CheckedCompileTime } else { *guard },
            body: *body,
            step: Some(*step),
            origin,
        };
        if let Some(iterations) = iterations {
            self.unroll_for(tails, plan, iterations)
        } else {
            self.loop_effect(tails, plan)
        }
    }

    fn loop_effect(&mut self, tails: Tails, plan: LoopPlan) -> Result<Tails, BuildError> {
        let LoopPlan { condition, guard, body, step, origin } = plan;
        let header = self.node(CfgNodeKind::LoopHeader, Some(origin));
        self.link(tails, header);
        let evaluated = self.evaluate(vec![(header, EdgeKind::Normal)], condition, origin)?;
        let branch_origin = self.expression_origin(condition, origin)?;
        let branch = self.node(CfgNodeKind::Branch { condition, guard }, Some(branch_origin));
        self.link(evaluated, branch);
        if guard == ControlGuard::DeferredScalar {
            self.active_deferred.push(branch);
        }
        let mut body_tails = self.block(vec![(branch, EdgeKind::True)], body)?;
        if let Some(step) = step {
            body_tails = self.block(body_tails, step)?;
        }
        if guard == ControlGuard::DeferredScalar {
            self.active_deferred.pop();
        }
        self.link(body_tails.into_iter().map(|(id, _)| (id, EdgeKind::Loop)).collect(), header);
        Ok(vec![(branch, EdgeKind::False)])
    }

    fn static_for_iterations(
        &self,
        initializer: BlockId,
        condition: ExprId,
        step: BlockId,
        body: BlockId,
    ) -> Option<usize> {
        let (variable, initial) = self.static_loop_initializer(initializer)?;
        let bound = self.static_loop_bound(condition, variable)?;
        if !self.static_loop_step(step, variable) {
            return None;
        }
        let body = self.hir.block(body)?;
        if body.effects.iter().any(|effect| Self::may_write_variable(effect, variable)) {
            return None;
        }
        let iterations = bound.saturating_sub(initial);
        let condition_span = self.hir.expression(condition)?.span;
        self.within_unroll_budget(iterations, body.effects.len(), body.span, condition_span)
            .then_some(iterations)
    }

    fn static_loop_initializer(&self, initializer: BlockId) -> Option<(SymbolId, usize)> {
        let initializer = self.hir.block(initializer)?;
        let mut initial = None;
        for effect in &initializer.effects {
            match effect {
                Effect::Declaration { .. } => {}
                Effect::VariableAssignment {
                    target,
                    value,
                    operator: AssignmentOperator::Assign,
                    ..
                } if target.steps.is_empty() => {
                    if initial.is_some() {
                        return None;
                    }
                    initial = Some((target.root, self.small_static_value(*value)?));
                }
                Effect::VariableAssignment { .. }
                | Effect::DeferredVariableAssignment { .. }
                | Effect::ComponentInstantiation { .. }
                | Effect::WitnessAssignment { .. }
                | Effect::ConstraintAssignment { .. }
                | Effect::OpaqueAssignment { .. }
                | Effect::EqualityConstraint { .. }
                | Effect::OpaqueEquality { .. }
                | Effect::Update { .. }
                | Effect::If { .. }
                | Effect::While { .. }
                | Effect::For { .. }
                | Effect::Return { .. }
                | Effect::Assert { .. }
                | Effect::DeferredAssert { .. }
                | Effect::Log { .. }
                | Effect::AnonymousComponent { .. }
                | Effect::Opaque { .. }
                | Effect::Block(_) => return None,
            }
        }
        initial
    }

    fn static_loop_bound(&self, condition: ExprId, variable: SymbolId) -> Option<usize> {
        let expression = self.hir.expression(condition)?;
        let ExprKind::Binary { operator: BinaryOperator::Less, left, right } = &expression.kind
        else {
            return None;
        };
        let ExprKind::Access(path) = &self.hir.expression(*left)?.kind else { return None };
        if path.root != variable || !path.steps.is_empty() {
            return None;
        }
        self.small_static_value(*right)
    }

    fn static_loop_step(&self, step: BlockId, variable: SymbolId) -> bool {
        let Some(step) = self.hir.block(step) else { return false };
        let [Effect::Update { target, operator: PostfixOperator::Increment, .. }] =
            step.effects.as_slice()
        else {
            return false;
        };
        target.root == variable && target.steps.is_empty()
    }

    fn small_static_value(&self, expression: ExprId) -> Option<usize> {
        let maximum = if self.scalar_seeds.is_some() { 512 } else { 16 };
        let value = match &self.hir.expression(expression)?.kind {
            ExprKind::Number(text) => text.parse::<usize>().ok()?,
            ExprKind::Access(path) => self.seeded_parameter_value(path)?,
            ExprKind::Binary { .. }
            | ExprKind::Unary { .. }
            | ExprKind::Ternary { .. }
            | ExprKind::Call { .. }
            | ExprKind::Array { .. }
            | ExprKind::Tuple { .. }
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Parallel(_)
            | ExprKind::Opaque(_) => return None,
        };
        (value <= maximum).then_some(value)
    }

    fn seeded_parameter_value(&self, path: &AccessPath) -> Option<usize> {
        if path.root != path.terminal || !path.steps.is_empty() {
            return None;
        }
        let symbol = self.hir.symbol(path.root)?;
        if symbol.kind != SymbolKind::Parameter || symbol.rank != 0 {
            return None;
        }
        if !self.parameter_is_stable(path.root) {
            return None;
        }
        self.scalar_seeds?.get(&path.root)?.as_bigint().to_usize()
    }

    fn parameter_is_stable(&self, parameter: SymbolId) -> bool {
        for block in self.hir.blocks() {
            for effect in &block.effects {
                let target = match effect {
                    Effect::VariableAssignment { target, .. }
                    | Effect::DeferredVariableAssignment { target, .. }
                    | Effect::OpaqueAssignment { target, .. }
                    | Effect::Update { target, .. } => Some(target),
                    Effect::Declaration { .. }
                    | Effect::ComponentInstantiation { .. }
                    | Effect::WitnessAssignment { .. }
                    | Effect::ConstraintAssignment { .. }
                    | Effect::EqualityConstraint { .. }
                    | Effect::OpaqueEquality { .. }
                    | Effect::If { .. }
                    | Effect::While { .. }
                    | Effect::For { .. }
                    | Effect::Return { .. }
                    | Effect::Assert { .. }
                    | Effect::DeferredAssert { .. }
                    | Effect::Log { .. }
                    | Effect::AnonymousComponent { .. }
                    | Effect::Opaque { .. }
                    | Effect::Block(_) => None,
                };
                if target.is_some_and(|path| path.root == parameter) {
                    return false;
                }
            }
        }
        true
    }

    fn within_unroll_budget(
        &self,
        iterations: usize,
        body_effects: usize,
        body_span: Span,
        condition_span: Span,
    ) -> bool {
        let expression_count = self
            .hir
            .expressions()
            .iter()
            .filter(|expression| {
                span_contains(body_span, expression.span)
                    || span_contains(condition_span, expression.span)
            })
            .count();
        let Some(per_effect) =
            expression_count.checked_add(1).and_then(|count| count.checked_mul(3))
        else {
            return false;
        };
        let Some(per_iteration) =
            body_effects.checked_add(4).and_then(|count| count.checked_mul(per_effect))
        else {
            return false;
        };
        let Some(nodes) = iterations
            .checked_mul(per_iteration)
            .and_then(|count| count.checked_add(self.nodes.len()))
        else {
            return false;
        };
        nodes <= 1_000_000
    }

    fn may_write_variable(effect: &Effect, variable: SymbolId) -> bool {
        match effect {
            Effect::VariableAssignment { target, .. }
            | Effect::DeferredVariableAssignment { target, .. }
            | Effect::Update { target, .. } => target.root == variable,
            Effect::Declaration { .. }
            | Effect::WitnessAssignment { .. }
            | Effect::ConstraintAssignment { .. }
            | Effect::EqualityConstraint { .. }
            | Effect::OpaqueEquality { .. }
            | Effect::Assert { .. }
            | Effect::DeferredAssert { .. }
            | Effect::Log { .. } => false,
            Effect::ComponentInstantiation { .. }
            | Effect::If { .. }
            | Effect::While { .. }
            | Effect::For { .. }
            | Effect::Return { .. }
            | Effect::AnonymousComponent { .. }
            | Effect::Block(_)
            | Effect::OpaqueAssignment { .. }
            | Effect::Opaque { .. } => true,
        }
    }

    fn unroll_for(
        &mut self,
        mut tails: Tails,
        plan: LoopPlan,
        iterations: usize,
    ) -> Result<Tails, BuildError> {
        let LoopPlan { condition, guard, body, step: Some(step), origin } = plan else {
            return Err(BuildError::InvalidLoopPlan);
        };
        let branch_origin = self.expression_origin(condition, origin)?;
        for _ in 0..iterations {
            let evaluated = self.evaluate(tails, condition, origin)?;
            let branch = self.node(CfgNodeKind::Branch { condition, guard }, Some(branch_origin));
            self.link(evaluated, branch);
            let body_tails = self.block(vec![(branch, EdgeKind::True)], body)?;
            tails = self.block(body_tails, step)?;
            if tails.is_empty() {
                return Ok(tails);
            }
        }
        let evaluated = self.evaluate(tails, condition, origin)?;
        let branch = self.node(CfgNodeKind::Branch { condition, guard }, Some(branch_origin));
        self.link(evaluated, branch);
        Ok(vec![(branch, EdgeKind::False)])
    }

    fn evaluate_target(
        &mut self,
        mut tails: Tails,
        target: &AccessPath,
        origin: Origin,
    ) -> Result<Tails, BuildError> {
        self.checked_paths.push(target.clone());
        for step in &target.steps {
            if let AccessStep::Index {
                index: parser::hir::ArrayIndex::Symbolic(expression), ..
            } = step
            {
                tails = self.evaluate(tails, *expression, origin)?;
            }
        }
        Ok(tails)
    }

    fn expression_origin(&self, expression: ExprId, origin: Origin) -> Result<Origin, BuildError> {
        let span =
            self.hir.expression(expression).ok_or(BuildError::MissingExpression(expression))?.span;
        Ok(Origin { expression: Some(expression), span, ..origin })
    }
}

fn span_contains(outer: Span, inner: Span) -> bool {
    outer.source() == inner.source() && outer.start() <= inner.start() && inner.end() <= outer.end()
}

fn definition_symbols(
    hir: &HirProject,
    definition: DefinitionRef,
) -> Result<(BlockId, BTreeSet<SymbolId>, &[SymbolId]), BuildError> {
    let (body, parameters, ports) = match definition {
        DefinitionRef::Function(id) => {
            let item = hir.function(id).ok_or(BuildError::ForeignDefinition)?;
            (item.body, item.parameters.as_slice(), &[][..])
        }
        DefinitionRef::Template(id) => {
            let item = hir.template(id).ok_or(BuildError::ForeignDefinition)?;
            (item.body, item.parameters.as_slice(), item.ports.as_slice())
        }
        DefinitionRef::Bus(id) => {
            let item = hir.bus(id).ok_or(BuildError::ForeignDefinition)?;
            (item.body, item.parameters.as_slice(), item.ports.as_slice())
        }
    };
    let mut symbols: BTreeSet<_> = parameters.iter().copied().collect();
    for port in ports {
        let port = hir.port(*port).ok_or(BuildError::MissingPort(*port))?;
        symbols.insert(port.symbol);
    }
    Ok((body, symbols, parameters))
}

fn effect_span(effect: &Effect, block_span: Span) -> Span {
    match effect {
        Effect::Declaration { span, .. }
        | Effect::VariableAssignment { span, .. }
        | Effect::DeferredVariableAssignment { span, .. }
        | Effect::ComponentInstantiation { span, .. }
        | Effect::WitnessAssignment { span, .. }
        | Effect::ConstraintAssignment { span, .. }
        | Effect::OpaqueAssignment { span, .. }
        | Effect::EqualityConstraint { span, .. }
        | Effect::OpaqueEquality { span, .. }
        | Effect::Update { span, .. }
        | Effect::If { span, .. }
        | Effect::While { span, .. }
        | Effect::For { span, .. }
        | Effect::Return { span, .. }
        | Effect::Assert { span, .. }
        | Effect::DeferredAssert { span, .. }
        | Effect::Log { span, .. }
        | Effect::AnonymousComponent { span, .. }
        | Effect::Opaque { span, .. } => *span,
        Effect::Block(_) => block_span,
    }
}

/// Build a CFG from a checked HIR definition.
///
/// # Errors
///
/// Returns a build error for a missing definition, malformed checked HIR, or invalid graph.
pub fn build_cfg(hir: &HirProject, definition: DefinitionRef) -> Result<DefinitionCfg, BuildError> {
    build_cfg_inner(hir, definition, None, None)
}

pub(crate) fn build_cfg_with_exact_calls(
    hir: &HirProject,
    definition: DefinitionRef,
    calls: &ScalarExpressionEvidence,
    scalar_seeds: &BTreeMap<SymbolId, FieldValue>,
) -> Result<DefinitionCfg, BuildError> {
    if !calls.belongs_to_definition(hir, definition) {
        return Err(BuildError::ForeignCallResults);
    }
    build_cfg_inner(hir, definition, Some(calls), Some(scalar_seeds))
}

fn build_cfg_inner<'a>(
    hir: &'a HirProject,
    definition: DefinitionRef,
    calls: Option<&'a ScalarExpressionEvidence>,
    scalar_seeds: Option<&'a BTreeMap<SymbolId, FieldValue>>,
) -> Result<DefinitionCfg, BuildError> {
    let (body, local_symbols, parameters) = definition_symbols(hir, definition)?;
    if let Some(values) = scalar_seeds {
        if values.keys().any(|symbol| !parameters.contains(symbol)) {
            return Err(BuildError::ForeignScalarSeeds);
        }
    }
    let mut builder = Builder {
        hir,
        calls,
        scalar_seeds,
        nodes: Vec::new(),
        edges: Vec::new(),
        conditions: BTreeMap::new(),
        active_deferred: Vec::new(),
        local_symbols,
        checked_paths: Vec::new(),
        exit: NodeId::new(1),
    };
    let entry = builder.node(CfgNodeKind::Entry, None);
    let exit = builder.node(CfgNodeKind::Exit, None);
    let tails = builder.block(vec![(entry, EdgeKind::Normal)], body)?;
    builder.link(tails, exit);
    let local_symbols = builder.local_symbols;
    let checked_paths = builder.checked_paths;
    let graph = IndexedGraph::new(builder.nodes, builder.edges, vec![entry], vec![exit])
        .map_err(BuildError::InvalidGraph)?;
    let topology = TopologyIndex::new(&graph);
    let mut evaluations: BTreeMap<ExprId, Vec<NodeId>> = BTreeMap::new();
    for id in graph.nodes() {
        if let Some(CfgNodeKind::Evaluate(expression)) = graph.node(*id).map(|node| &node.kind) {
            evaluations.entry(*expression).or_default().push(*id);
        }
    }
    Ok(DefinitionCfg {
        graph,
        topology,
        evaluations,
        local_symbols,
        checked_paths,
        scalar_seeds: scalar_seeds.cloned(),
        definition,
        entry,
        exit,
    })
}
