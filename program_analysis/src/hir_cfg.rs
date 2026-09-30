//! Immutable control flow graphs over the checked HIR.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{EdgeId, EdgeRef, FlowGraph, GraphError, IndexedGraph, NodeId};
use parser::hir::{
    AccessPath, AccessStep, BlockId, ControlGuard, DefinitionRef, Effect, ExprId, ExprKind,
    HirProject, IncompleteReason, SymbolId,
};
use parser::new_frontend::{BinaryOperator, PostfixOperator, Span};

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
    Branch { condition: ExprId, guard: ControlGuard },
    Witness { target: AccessPath, value: ExprId },
    Constraint { target: Option<AccessPath>, left: ExprId, right: Option<ExprId> },
    Assignment { target: AccessPath, value: ExprId },
    Update { target: AccessPath, operator: PostfixOperator },
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
    pub kind: EdgeKind,
    pub condition: Option<ExprId>,
    pub guard: Option<ControlGuard>,
}

pub struct DefinitionCfg {
    graph: IndexedGraph<CfgNode, CfgEdge>,
    local_symbols: BTreeSet<SymbolId>,
    checked_paths: Vec<AccessPath>,
    pub definition: DefinitionRef,
    pub entry: NodeId,
    pub exit: NodeId,
}

impl DefinitionCfg {
    pub(crate) fn owns_symbol(&self, symbol: SymbolId) -> bool {
        self.local_symbols.contains(&symbol)
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

struct Builder<'a> {
    hir: &'a HirProject,
    nodes: Vec<CfgNode>,
    edges: Vec<(NodeId, NodeId, CfgEdge)>,
    conditions: BTreeMap<NodeId, (ExprId, ControlGuard)>,
    active_deferred: Vec<NodeId>,
    local_symbols: BTreeSet<SymbolId>,
    checked_paths: Vec<AccessPath>,
    exit: NodeId,
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
            self.edges.push((source, node, CfgEdge { kind, condition, guard }));
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
        let mut value_control = None;
        match &expr.kind {
            ExprKind::Number(_) | ExprKind::Opaque(_) => {}
            ExprKind::Access(path) => {
                self.checked_paths.push(path.clone());
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
                let guard = if expr.knownness == parser::hir::Knownness::Constant {
                    ControlGuard::CheckedCompileTime
                } else {
                    ControlGuard::DeferredScalar
                };
                let branch = self.node(
                    CfgNodeKind::Branch { condition: *condition, guard },
                    Some(branch_origin),
                );
                self.link(tails, branch);
                if guard == ControlGuard::DeferredScalar {
                    self.active_deferred.push(branch);
                }
                let yes_tail = self.evaluate(vec![(branch, EdgeKind::True)], *yes, origin)?;
                let no_tail = self.evaluate(vec![(branch, EdgeKind::False)], *no, origin)?;
                if guard == ControlGuard::DeferredScalar {
                    self.active_deferred.pop();
                    value_control = Some(branch);
                }
                tails = [yes_tail, no_tail].concat();
            }
        }
        let origin = Origin { expression: Some(id), span: expr.span, ..origin };
        if let Some(branch) = value_control {
            self.active_deferred.push(branch);
        }
        let tails = self.append(tails, CfgNodeKind::Evaluate(id), origin);
        if value_control.is_some() {
            self.active_deferred.pop();
        }
        Ok(tails)
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
                self.local_symbols.insert(*symbol);
                let mut tails = tails;
                for &dimension in &declared.dimensions {
                    tails = self.evaluate(tails, dimension, origin)?;
                }
                Ok(self.append(tails, CfgNodeKind::Declaration, origin))
            }
            Effect::VariableAssignment { .. }
            | Effect::ComponentInstantiation { .. }
            | Effect::WitnessAssignment { .. }
            | Effect::ConstraintAssignment { .. } => self.assignment_effect(tails, effect, origin),
            Effect::EqualityConstraint { left, right, .. } => {
                let tails = self.evaluate(tails, *left, origin)?;
                let tails = self.evaluate(tails, *right, origin)?;
                Ok(self.append(
                    tails,
                    CfgNodeKind::Constraint { target: None, left: *left, right: Some(*right) },
                    Origin { expression: Some(*left), ..origin },
                ))
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

    fn assignment_effect(
        &mut self,
        tails: Tails,
        effect: &Effect,
        origin: Origin,
    ) -> Result<Tails, BuildError> {
        let (target, value) = match effect {
            Effect::VariableAssignment { target, value, .. }
            | Effect::ComponentInstantiation { target, value, .. }
            | Effect::WitnessAssignment { target, value, .. }
            | Effect::ConstraintAssignment { target, value, .. } => (target, *value),
            _ => return Err(BuildError::UnexpectedEffect),
        };
        let tails = self.evaluate_target(tails, target, origin)?;
        let tails = self.evaluate(tails, value, origin)?;
        let effect_origin = Origin { expression: Some(value), ..origin };
        match effect {
            Effect::VariableAssignment { .. } => Ok(self.append(
                tails,
                CfgNodeKind::Assignment { target: target.clone(), value },
                effect_origin,
            )),
            Effect::ComponentInstantiation { .. } => Ok(self.append(
                tails,
                CfgNodeKind::Instantiate { target: target.clone(), value },
                effect_origin,
            )),
            Effect::WitnessAssignment { .. } => Ok(self.append(
                tails,
                CfgNodeKind::Witness { target: target.clone(), value },
                effect_origin,
            )),
            Effect::ConstraintAssignment { .. } => {
                let tails = self.append(
                    tails,
                    CfgNodeKind::Witness { target: target.clone(), value },
                    effect_origin,
                );
                Ok(self.append(
                    tails,
                    CfgNodeKind::Constraint {
                        target: Some(target.clone()),
                        left: value,
                        right: None,
                    },
                    effect_origin,
                ))
            }
            _ => Err(BuildError::UnexpectedEffect),
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
        let iterations = if *guard == ControlGuard::CheckedCompileTime {
            self.static_for_iterations(*initializer, *condition, *step, *body)
        } else {
            None
        };
        let tails = self.block(tails, *initializer)?;
        let plan = LoopPlan {
            condition: *condition,
            guard: *guard,
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
        let initializer = self.hir.block(initializer)?;
        let mut initial = None;
        for effect in &initializer.effects {
            match effect {
                Effect::Declaration { .. } => {}
                Effect::VariableAssignment { target, value, .. } if target.steps.is_empty() => {
                    if initial.is_some() {
                        return None;
                    }
                    initial = Some((target.root, self.small_literal(*value)?));
                }
                _ => return None,
            }
        }
        let (variable, initial) = initial?;
        let expression = self.hir.expression(condition)?;
        let ExprKind::Binary { operator: BinaryOperator::Less, left, right } = &expression.kind
        else {
            return None;
        };
        let ExprKind::Access(path) = &self.hir.expression(*left)?.kind else { return None };
        if path.root != variable || !path.steps.is_empty() {
            return None;
        }
        let bound = self.small_literal(*right)?;
        let step = self.hir.block(step)?;
        let [Effect::Update { target, operator: PostfixOperator::Increment, .. }] =
            step.effects.as_slice()
        else {
            return None;
        };
        if target.root != variable || !target.steps.is_empty() {
            return None;
        }
        let body = self.hir.block(body)?;
        if body.effects.iter().any(|effect| Self::may_write_variable(effect, variable)) {
            return None;
        }
        let iterations = bound.saturating_sub(initial);
        (iterations <= 16).then_some(iterations)
    }

    fn small_literal(&self, expression: ExprId) -> Option<usize> {
        let ExprKind::Number(text) = &self.hir.expression(expression)?.kind else { return None };
        let value = text.parse::<usize>().ok()?;
        (value <= 16).then_some(value)
    }

    fn may_write_variable(effect: &Effect, variable: SymbolId) -> bool {
        match effect {
            Effect::VariableAssignment { target, .. } | Effect::Update { target, .. } => {
                target.root == variable
            }
            Effect::Declaration { .. }
            | Effect::WitnessAssignment { .. }
            | Effect::ConstraintAssignment { .. }
            | Effect::EqualityConstraint { .. }
            | Effect::Assert { .. }
            | Effect::Log { .. } => false,
            Effect::ComponentInstantiation { .. }
            | Effect::If { .. }
            | Effect::While { .. }
            | Effect::For { .. }
            | Effect::Return { .. }
            | Effect::AnonymousComponent { .. }
            | Effect::Block(_)
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

fn definition_symbols(
    hir: &HirProject,
    definition: DefinitionRef,
) -> Result<(BlockId, BTreeSet<SymbolId>), BuildError> {
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
    Ok((body, symbols))
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
    let (body, local_symbols) = definition_symbols(hir, definition)?;
    let mut builder = Builder {
        hir,
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
    Ok(DefinitionCfg { graph, local_symbols, checked_paths, definition, entry, exit })
}
