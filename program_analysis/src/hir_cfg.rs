//! Immutable control flow graphs over the checked HIR.

use std::collections::BTreeMap;

use abstract_interpretation::graph::{EdgeId, EdgeRef, FlowGraph, GraphError, IndexedGraph, NodeId};
use parser::hir::{
    AccessPath, AccessStep, BlockId, DefinitionRef, Effect, ExprId, ExprKind, HirProject,
    IncompleteReason, SymbolId,
};
use parser::new_frontend::Span;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Origin {
    pub block: BlockId,
    pub effect_index: usize,
    pub expression: Option<ExprId>,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CfgNodeKind {
    Entry,
    Exit,
    Evaluate(ExprId),
    LoopHeader,
    Branch(ExprId),
    Witness { target: AccessPath, value: ExprId },
    Constraint { target: Option<AccessPath>, left: ExprId, right: Option<ExprId> },
    Assignment { target: AccessPath, value: ExprId },
    Instantiate { target: AccessPath, value: ExprId },
    Declaration,
    Return(ExprId),
    Assert { condition: ExprId },
    Log,
    Opaque(IncompleteReason),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CfgNode {
    pub id: NodeId,
    pub kind: CfgNodeKind,
    pub origin: Option<Origin>,
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
    pub kind: EdgeKind,
    pub condition: Option<ExprId>,
}

pub struct DefinitionCfg {
    graph: IndexedGraph<CfgNode, CfgEdge>,
    pub definition: DefinitionRef,
    pub entry: NodeId,
    pub exit: NodeId,
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
    MissingBlock(BlockId),
    MissingExpression(ExprId),
    MissingSymbol(SymbolId),
    InvalidGraph(GraphError<NodeId, EdgeId>),
}

type Tails = Vec<(NodeId, EdgeKind)>;

struct Builder<'a> {
    hir: &'a HirProject,
    nodes: Vec<CfgNode>,
    edges: Vec<(NodeId, NodeId, CfgEdge)>,
    conditions: BTreeMap<NodeId, ExprId>,
    exit: NodeId,
}

impl Builder<'_> {
    fn node(&mut self, kind: CfgNodeKind, origin: Option<Origin>) -> NodeId {
        let id = NodeId::new(self.nodes.len());
        if let CfgNodeKind::Branch(condition) = &kind {
            self.conditions.insert(id, *condition);
        }
        self.nodes.push(CfgNode { id, kind, origin });
        id
    }

    fn link(&mut self, tails: Tails, node: NodeId) {
        for (source, kind) in tails {
            let condition = self.conditions.get(&source).copied();
            self.edges.push((source, node, CfgEdge { kind, condition }));
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
        let expr = self.hir.expression(id).ok_or(BuildError::MissingExpression(id))?;
        match &expr.kind {
            ExprKind::Number(_) | ExprKind::Opaque(_) => {}
            ExprKind::Access(path) => {
                for step in &path.steps {
                    if let AccessStep::Index {
                        index: parser::hir::ArrayIndex::Symbolic(index),
                        ..
                    } = step
                    {
                        tails = self.evaluate(tails, *index, origin)?;
                    }
                }
            }
            ExprKind::Call { arguments, .. } => {
                for &argument in arguments {
                    tails = self.evaluate(tails, argument, origin)?;
                }
            }
            ExprKind::AnonymousComponent { arguments, inputs, .. } => {
                for &argument in arguments {
                    tails = self.evaluate(tails, argument, origin)?;
                }
                for input in inputs {
                    tails = self.evaluate(tails, input.value, origin)?;
                }
            }
            ExprKind::Array(values) | ExprKind::Tuple(values) => {
                for &value in values {
                    tails = self.evaluate(tails, value, origin)?;
                }
            }
            ExprKind::Unary { operand, .. } | ExprKind::Parallel(operand) => {
                tails = self.evaluate(tails, *operand, origin)?;
            }
            ExprKind::Binary { left, right, .. } => {
                tails = self.evaluate(tails, *left, origin)?;
                tails = self.evaluate(tails, *right, origin)?;
            }
            ExprKind::Ternary { condition, yes, no } => {
                tails = self.evaluate(tails, *condition, origin)?;
                let branch_origin = self.expression_origin(*condition, origin)?;
                let branch = self.node(CfgNodeKind::Branch(*condition), Some(branch_origin));
                self.link(tails, branch);
                let yes_tail = self.evaluate(vec![(branch, EdgeKind::True)], *yes, origin)?;
                let no_tail = self.evaluate(vec![(branch, EdgeKind::False)], *no, origin)?;
                tails = [yes_tail, no_tail].concat();
            }
        }
        let origin = Origin { expression: Some(id), span: expr.span, ..origin };
        Ok(self.append(tails, CfgNodeKind::Evaluate(id), origin))
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
            Effect::Declaration { symbol, .. } => {
                let declared =
                    self.hir.symbol(*symbol).ok_or(BuildError::MissingSymbol(*symbol))?;
                let mut tails = tails;
                for &dimension in &declared.dimensions {
                    tails = self.evaluate(tails, dimension, origin)?;
                }
                Ok(self.append(tails, CfgNodeKind::Declaration, origin))
            }
            Effect::VariableAssignment { target, value, .. } => {
                let tails = self.evaluate_target(tails, target, origin)?;
                let tails = self.evaluate(tails, *value, origin)?;
                Ok(self.append(
                    tails,
                    CfgNodeKind::Assignment { target: target.clone(), value: *value },
                    origin,
                ))
            }
            Effect::ComponentInstantiation { target, value, .. } => {
                let tails = self.evaluate_target(tails, target, origin)?;
                let tails = self.evaluate(tails, *value, origin)?;
                Ok(self.append(
                    tails,
                    CfgNodeKind::Instantiate { target: target.clone(), value: *value },
                    origin,
                ))
            }
            Effect::WitnessAssignment { target, value, .. }
            | Effect::ConstraintAssignment { target, value, .. } => {
                let tails = self.evaluate_target(tails, target, origin)?;
                let tails = self.evaluate(tails, *value, origin)?;
                let effect_origin = Origin { expression: Some(*value), ..origin };
                let tails = self.append(
                    tails,
                    CfgNodeKind::Witness { target: target.clone(), value: *value },
                    effect_origin,
                );
                if let Effect::ConstraintAssignment { .. } = effect {
                    Ok(self.append(
                        tails,
                        CfgNodeKind::Constraint {
                            target: Some(target.clone()),
                            left: *value,
                            right: None,
                        },
                        effect_origin,
                    ))
                } else {
                    Ok(tails)
                }
            }
            Effect::EqualityConstraint { left, right, .. } => {
                let tails = self.evaluate(tails, *left, origin)?;
                let tails = self.evaluate(tails, *right, origin)?;
                Ok(self.append(
                    tails,
                    CfgNodeKind::Constraint { target: None, left: *left, right: Some(*right) },
                    Origin { expression: Some(*left), ..origin },
                ))
            }
            Effect::Update { .. } => Ok(self.append(
                tails,
                CfgNodeKind::Opaque(IncompleteReason::Unsupported("update transfer".into())),
                origin,
            )),
            Effect::If { condition, then_block, else_block, .. } => {
                let tails = self.evaluate(tails, *condition, origin)?;
                let branch_origin = self.expression_origin(*condition, origin)?;
                let branch = self.node(CfgNodeKind::Branch(*condition), Some(branch_origin));
                self.link(tails, branch);
                let then_tails = self.block(vec![(branch, EdgeKind::True)], *then_block)?;
                let else_tails = if let Some(other) = else_block {
                    self.block(vec![(branch, EdgeKind::False)], *other)?
                } else {
                    vec![(branch, EdgeKind::False)]
                };
                Ok([then_tails, else_tails].concat())
            }
            Effect::While { condition, body, .. } => {
                self.loop_effect(tails, *condition, *body, None, origin)
            }
            Effect::For { initializer, condition, step, body, .. } => {
                let tails = self.block(tails, *initializer)?;
                self.loop_effect(tails, *condition, *body, Some(*step), origin)
            }
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

    fn loop_effect(
        &mut self,
        tails: Tails,
        condition: ExprId,
        body: BlockId,
        step: Option<BlockId>,
        origin: Origin,
    ) -> Result<Tails, BuildError> {
        let header = self.node(CfgNodeKind::LoopHeader, Some(origin));
        self.link(tails, header);
        let evaluated = self.evaluate(vec![(header, EdgeKind::Normal)], condition, origin)?;
        let branch_origin = self.expression_origin(condition, origin)?;
        let branch = self.node(CfgNodeKind::Branch(condition), Some(branch_origin));
        self.link(evaluated, branch);
        let mut body_tails = self.block(vec![(branch, EdgeKind::True)], body)?;
        if let Some(step) = step {
            body_tails = self.block(body_tails, step)?;
        }
        self.link(body_tails.into_iter().map(|(id, _)| (id, EdgeKind::Loop)).collect(), header);
        Ok(vec![(branch, EdgeKind::False)])
    }

    fn evaluate_target(
        &mut self,
        mut tails: Tails,
        target: &AccessPath,
        origin: Origin,
    ) -> Result<Tails, BuildError> {
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

fn effect_span(effect: &Effect, block_span: Span) -> Span {
    match effect {
        Effect::Declaration { span, .. }
        | Effect::VariableAssignment { span, .. }
        | Effect::ComponentInstantiation { span, .. }
        | Effect::WitnessAssignment { span, .. }
        | Effect::ConstraintAssignment { span, .. }
        | Effect::EqualityConstraint { span, .. }
        | Effect::Update { span, .. }
        | Effect::If { span, .. }
        | Effect::While { span, .. }
        | Effect::For { span, .. }
        | Effect::Return { span, .. }
        | Effect::Assert { span, .. }
        | Effect::Log { span, .. }
        | Effect::AnonymousComponent { span, .. }
        | Effect::Opaque { span, .. } => *span,
        Effect::Block(_) => block_span,
    }
}

/// Lower a checked HIR definition without changing the legacy analysis path.
pub fn build_cfg(hir: &HirProject, definition: DefinitionRef) -> Result<DefinitionCfg, BuildError> {
    let body = match definition {
        DefinitionRef::Function(id) => hir.function(id).ok_or(BuildError::ForeignDefinition)?.body,
        DefinitionRef::Template(id) => hir.template(id).ok_or(BuildError::ForeignDefinition)?.body,
        DefinitionRef::Bus(id) => hir.bus(id).ok_or(BuildError::ForeignDefinition)?.body,
    };
    let mut builder = Builder {
        hir,
        nodes: Vec::new(),
        edges: Vec::new(),
        conditions: BTreeMap::new(),
        exit: NodeId::new(1),
    };
    let entry = builder.node(CfgNodeKind::Entry, None);
    let exit = builder.node(CfgNodeKind::Exit, None);
    let tails = builder.block(vec![(entry, EdgeKind::Normal)], body)?;
    builder.link(tails, exit);
    let graph = IndexedGraph::new(builder.nodes, builder.edges, vec![entry], vec![exit])
        .map_err(BuildError::InvalidGraph)?;
    Ok(DefinitionCfg { graph, definition, entry, exit })
}
