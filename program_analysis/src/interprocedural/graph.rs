use std::collections::BTreeSet;

use parser::hir::{
    AccessPath, AccessStep, AnonymousInputEffect, ArrayIndex, BlockId, CallTarget, ComponentId,
    ControlGuard, DefinitionRef, Effect, ExprId, ExprKind, HirProject, IncompleteReason, SymbolId,
};
use parser::new_frontend::Span;

/// The definition or root whose source contains a call.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CallOwner {
    Definition(DefinitionRef),
    Main(usize),
}

/// Source validation of a may-call site; reachability is checked in the CFG.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CallProvenance {
    EffectOwned,
    Provisional,
    Unattached,
}

/// A source call, including unresolved calls that cannot support a summary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallSite {
    pub owner: CallOwner,
    pub target: CallTarget,
    pub expression: Option<ExprId>,
    pub span: Span,
    pub provenance: CallProvenance,
}

impl CallSite {
    /// Returns the checked callee ID, if resolution succeeded.
    #[must_use]
    pub fn resolved(&self) -> Option<DefinitionRef> {
        match self.target {
            CallTarget::Function(id) => Some(DefinitionRef::Function(id)),
            CallTarget::Template(id) => Some(DefinitionRef::Template(id)),
            CallTarget::Missing { .. }
            | CallTarget::WrongKind { .. }
            | CallTarget::Ambiguous { .. }
            | CallTarget::Opaque { .. } => None,
        }
    }
}

/// Deterministic call sites. An empty graph is valid for a library without `main`.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct CallGraph {
    sites: Vec<CallSite>,
}

impl CallGraph {
    #[must_use]
    pub fn sites(&self) -> &[CallSite] {
        &self.sites
    }

    #[must_use]
    pub fn calls_from(&self, owner: CallOwner) -> Vec<&CallSite> {
        self.sites.iter().filter(|site| site.owner == owner).collect()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CallGraphError {
    MissingBlock(BlockId),
    MissingExpression(ExprId),
    MissingComponent(ComponentId),
    MissingSymbol(SymbolId),
}

/// Builds call sites from every effect-owned expression and nested block.
///
/// # Errors
/// Returns an error if an HIR reference is missing or belongs to another project.
pub fn build_call_graph(hir: &HirProject) -> Result<CallGraph, CallGraphError> {
    let mut graph = CallGraph::default();
    for function in hir.functions() {
        let mut scanner = Scanner::new(
            hir,
            &mut graph,
            CallOwner::Definition(DefinitionRef::Function(function.id)),
        );
        scanner.block(function.body)?;
        scanner.unattached(function.span)?;
    }
    for template in hir.templates() {
        let mut scanner = Scanner::new(
            hir,
            &mut graph,
            CallOwner::Definition(DefinitionRef::Template(template.id)),
        );
        scanner.block(template.body)?;
        scanner.unattached(template.span)?;
    }
    for bus in hir.buses() {
        let mut scanner =
            Scanner::new(hir, &mut graph, CallOwner::Definition(DefinitionRef::Bus(bus.id)));
        scanner.block(bus.body)?;
        scanner.unattached(bus.span)?;
    }
    for (index, main) in hir.mains.iter().enumerate() {
        graph.sites.push(CallSite {
            owner: CallOwner::Main(index),
            target: main.target.clone(),
            expression: None,
            span: main.span,
            provenance: CallProvenance::EffectOwned,
        });
        let mut scanner = Scanner::new(hir, &mut graph, CallOwner::Main(index));
        for argument in &main.arguments {
            scanner.expression(*argument)?;
        }
    }
    Ok(graph)
}

struct Scanner<'a> {
    hir: &'a HirProject,
    graph: &'a mut CallGraph,
    owner: CallOwner,
    seen_blocks: BTreeSet<BlockId>,
    seen_expressions: BTreeSet<ExprId>,
    provenance: CallProvenance,
}

impl<'a> Scanner<'a> {
    fn new(hir: &'a HirProject, graph: &'a mut CallGraph, owner: CallOwner) -> Self {
        Self {
            hir,
            graph,
            owner,
            seen_blocks: BTreeSet::new(),
            seen_expressions: BTreeSet::new(),
            provenance: CallProvenance::EffectOwned,
        }
    }

    fn unattached(&mut self, span: Span) -> Result<(), CallGraphError> {
        self.provenance = CallProvenance::Unattached;
        let expressions: Vec<_> = self
            .hir
            .expressions()
            .iter()
            .filter(|expression| {
                expression.span.source() == span.source()
                    && expression.span.start() >= span.start()
                    && expression.span.end() <= span.end()
                    && !self.seen_expressions.contains(&expression.id)
            })
            .map(|expression| expression.id)
            .collect();
        for id in expressions {
            self.expression(id)?;
        }
        Ok(())
    }

    fn block(&mut self, id: BlockId) -> Result<(), CallGraphError> {
        if !self.seen_blocks.insert(id) {
            return Ok(());
        }
        let block = self.hir.block(id).ok_or(CallGraphError::MissingBlock(id))?;
        for effect in &block.effects {
            self.effect(effect)?;
        }
        Ok(())
    }

    fn effect(&mut self, effect: &Effect) -> Result<(), CallGraphError> {
        match effect {
            Effect::Declaration { symbol, .. } => {
                let symbol =
                    self.hir.symbol(*symbol).ok_or(CallGraphError::MissingSymbol(*symbol))?;
                for id in symbol.dimensions.iter().chain(&symbol.bus_arguments) {
                    self.expression(*id)?;
                }
            }
            Effect::VariableAssignment { target, value, .. }
            | Effect::ComponentInstantiation { target, value, .. }
            | Effect::WitnessAssignment { target, value, .. }
            | Effect::ConstraintAssignment { target, value, .. } => {
                self.path(target)?;
                self.expression(*value)?;
            }
            Effect::DeferredVariableAssignment { target, value, .. }
            | Effect::OpaqueAssignment { target, value, .. } => {
                self.provisional(|scanner| {
                    scanner.path(target)?;
                    scanner.expression(*value)
                })?;
            }
            Effect::EqualityConstraint { left, right, .. } => {
                self.expression(*left)?;
                self.expression(*right)?;
            }
            Effect::OpaqueEquality { left, right, .. } => {
                self.provisional(|scanner| {
                    scanner.expression(*left)?;
                    scanner.expression(*right)
                })?;
            }
            Effect::Update { target, .. } => self.path(target)?,
            Effect::If { condition, guard, then_block, else_block, .. } => {
                self.if_effect(*condition, *guard, *then_block, *else_block)?
            }
            Effect::While { condition, guard, body, .. } => {
                self.control(*guard, |scanner| {
                    scanner.expression(*condition)?;
                    scanner.block(*body)
                })?;
            }
            Effect::For { initializer, condition, guard, step, body, .. } => {
                self.block(*initializer)?;
                self.control(*guard, |scanner| {
                    scanner.expression(*condition)?;
                    scanner.block(*body)?;
                    scanner.block(*step)
                })?;
            }
            Effect::Return { value, .. } | Effect::AnonymousComponent { expression: value, .. } => {
                self.expression(*value)?
            }
            Effect::Assert { condition, .. } => self.expression(*condition)?,
            Effect::Log { values, .. } => {
                for value in values {
                    self.expression(*value)?;
                }
            }
            Effect::Block(id) => self.block(*id)?,
            Effect::Opaque { .. } => {}
        }
        Ok(())
    }

    fn if_effect(
        &mut self,
        condition: ExprId,
        guard: ControlGuard,
        then_block: BlockId,
        else_block: Option<BlockId>,
    ) -> Result<(), CallGraphError> {
        self.control(guard, |scanner| {
            scanner.expression(condition)?;
            scanner.block(then_block)?;
            if let Some(id) = else_block {
                scanner.block(id)?;
            }
            Ok(())
        })
    }

    fn control(
        &mut self,
        guard: ControlGuard,
        work: impl FnOnce(&mut Self) -> Result<(), CallGraphError>,
    ) -> Result<(), CallGraphError> {
        match guard {
            ControlGuard::DeferredScalar => self.provisional(work),
            ControlGuard::CheckedCompileTime | ControlGuard::WitnessOnly => work(self),
        }
    }

    fn provisional(
        &mut self,
        work: impl FnOnce(&mut Self) -> Result<(), CallGraphError>,
    ) -> Result<(), CallGraphError> {
        let previous = self.provenance;
        if self.provenance == CallProvenance::EffectOwned {
            self.provenance = CallProvenance::Provisional;
        }
        let result = work(self);
        self.provenance = previous;
        result
    }

    fn path(&mut self, path: &AccessPath) -> Result<(), CallGraphError> {
        for step in &path.steps {
            if let AccessStep::Index { index: ArrayIndex::Symbolic(id), .. } = step {
                self.expression(*id)?;
            }
        }
        Ok(())
    }

    fn expression(&mut self, id: ExprId) -> Result<(), CallGraphError> {
        if !self.seen_expressions.insert(id) {
            return Ok(());
        }
        let expression = self.hir.expression(id).ok_or(CallGraphError::MissingExpression(id))?;
        match &expression.kind {
            ExprKind::Number(_) | ExprKind::Opaque(_) => {}
            ExprKind::Access(path) => self.path(path)?,
            ExprKind::Call { target, arguments } => {
                self.record(target.clone(), Some(id), expression.span);
                self.expressions(arguments)?;
            }
            ExprKind::AnonymousComponent { component, arguments, inputs } => {
                let component = self
                    .hir
                    .component(*component)
                    .ok_or(CallGraphError::MissingComponent(*component))?;
                let target = component
                    .target
                    .clone()
                    .unwrap_or(CallTarget::Opaque { reason: IncompleteReason::UnknownType });
                self.record(target, Some(id), expression.span);
                self.expressions(arguments)?;
                self.anonymous_inputs(inputs)?;
            }
            ExprKind::Array(values) | ExprKind::Tuple(values) => self.expressions(values)?,
            ExprKind::Unary { operand, .. } | ExprKind::Parallel(operand) => {
                self.expression(*operand)?;
            }
            ExprKind::Binary { left, right, .. } => {
                self.expression(*left)?;
                self.expression(*right)?;
            }
            ExprKind::Ternary { condition, yes, no } => {
                self.expression(*condition)?;
                self.expression(*yes)?;
                self.expression(*no)?;
            }
        }
        Ok(())
    }

    fn expressions(&mut self, ids: &[ExprId]) -> Result<(), CallGraphError> {
        for id in ids {
            self.expression(*id)?;
        }
        Ok(())
    }

    fn anonymous_inputs(&mut self, inputs: &[AnonymousInputEffect]) -> Result<(), CallGraphError> {
        for input in inputs {
            self.expression(input.value)?;
        }
        Ok(())
    }

    fn record(&mut self, target: CallTarget, expression: Option<ExprId>, span: Span) {
        self.graph.sites.push(CallSite {
            owner: self.owner,
            target,
            expression,
            span,
            provenance: self.provenance,
        });
    }
}
