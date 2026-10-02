//! Validate access bounds and assignment ranks in one concrete argument context.

use std::cell::RefCell;
use std::collections::BTreeMap;

use abstract_interpretation::graph::FlowGraph;
use num_traits::ToPrimitive;
use parser::hir::{
    AccessPath, AccessStep, ArrayIndex, ExprId, ExprKind, SemanticCode, SemanticDiagnostic,
    Severity, SymbolId,
};
use parser::new_frontend::{AssignmentOperator, Span};

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::{AnalysisFacts, Fact, FieldContext, Range};
use crate::interprocedural::{
    AnalyzeEvidenceError, ArgumentShape, ArgumentValue, CallContext, ProjectSummaries,
    SummaryBlocker,
};
use crate::interprocedural::context::MAX_ARGUMENT_DEPTH;

#[derive(Clone, Copy)]
enum ShapeError {
    ScalarIndex,
    IndexOutOfBounds,
    AssignmentRank,
    AggregateUpdate,
}

#[derive(Clone, Copy)]
enum FailureSubject {
    ScalarAssignment(ExprId),
    ValueUse(SymbolId),
}

pub(super) struct ShapeFailure {
    subject: FailureSubject,
    span: Span,
    error: ShapeError,
}

impl ShapeFailure {
    pub fn diagnostic(&self) -> SemanticDiagnostic {
        let (code, message) = match self.error {
            ShapeError::ScalarIndex => {
                (SemanticCode::InvalidArrayAccess, "cannot index a scalar parameter argument")
            }
            ShapeError::IndexOutOfBounds => {
                (SemanticCode::InvalidArrayAccess, "parameter index exceeds the argument bounds")
            }
            ShapeError::AssignmentRank => (
                SemanticCode::InvalidAssignment,
                "assignment value has a different rank than its target",
            ),
            ShapeError::AggregateUpdate => {
                (SemanticCode::InvalidAssignment, "arithmetic update requires a scalar parameter")
            }
        };
        let message = match self.subject {
            FailureSubject::ScalarAssignment(_) => {
                "a scalar variable assignment received an aggregate argument"
            }
            FailureSubject::ValueUse(_) => message,
        };
        SemanticDiagnostic {
            code,
            severity: Severity::Error,
            span: self.span,
            message: message.into(),
            expected_kind: None,
            actual_kind: None,
        }
    }

    pub fn summary_blocker(&self) -> SummaryBlocker {
        match self.subject {
            FailureSubject::ScalarAssignment(value) => SummaryBlocker::InvalidAssignment(value),
            FailureSubject::ValueUse(symbol) => SummaryBlocker::InvalidValueUse(symbol),
        }
    }

    pub fn into_analysis_error(self, context: &CallContext) -> AnalyzeEvidenceError {
        let diagnostic = Box::new(self.diagnostic());
        let context = Box::new(context.clone());
        match self.subject {
            FailureSubject::ScalarAssignment(_) => {
                AnalyzeEvidenceError::InvalidAssignment { context, diagnostic }
            }
            FailureSubject::ValueUse(_) => {
                AnalyzeEvidenceError::InvalidValueUse { context, diagnostic }
            }
        }
    }
}

struct ShapeValidator<'a, 'hir> {
    arguments: BTreeMap<SymbolId, &'a ArgumentValue>,
    facts: &'a AnalysisFacts<'hir>,
    field: &'a FieldContext,
    ranges: RefCell<BTreeMap<ExprId, Fact<Range>>>,
}

impl ProjectSummaries<'_> {
    pub(super) fn invalid_value_use(
        &self,
        parameters: &[SymbolId],
        context: &CallContext,
        facts: &AnalysisFacts<'_>,
    ) -> Option<ShapeFailure> {
        let validator = ShapeValidator {
            arguments: parameters.iter().copied().zip(context.arguments()).collect(),
            facts,
            field: self.field_context(),
            ranges: RefCell::new(BTreeMap::new()),
        };
        for id in facts.cfg().nodes() {
            let Some(node) = facts.cfg().node(*id) else { continue };
            let Some(failure) = validator.node_failure(&node.kind) else { continue };
            if facts.required_evaluation(*id).certified() != Some(&true) {
                continue;
            }
            return Some(failure);
        }
        None
    }
}

impl ShapeValidator<'_, '_> {
    fn range(&self, expression: ExprId) -> Fact<Range> {
        let cached = self.ranges.borrow().get(&expression).cloned();
        if let Some(cached) = cached {
            return cached;
        }
        let fact = self.facts.range(expression);
        self.ranges.borrow_mut().insert(expression, fact.clone());
        fact
    }

    fn node_failure(&self, kind: &CfgNodeKind) -> Option<ShapeFailure> {
        match kind {
            CfgNodeKind::Evaluate(id) => {
                let ExprKind::Access(path) = &self.facts.hir().expression(*id)?.kind else {
                    return None;
                };
                self.access_rank(path).err().map(|error| self.failure(path, error))
            }
            CfgNodeKind::Assignment { target, value, operator }
            | CfgNodeKind::DeferredAssignment { target, value, operator }
            | CfgNodeKind::OpaqueAssignment { target, value, operator, .. } => {
                self.assignment_failure(target, *value, *operator)
            }
            CfgNodeKind::Update { target, .. } => match self.access_rank(target) {
                Err(error) => Some(self.failure(target, error)),
                Ok(Some(rank)) if rank > 0 => {
                    Some(self.failure(target, ShapeError::AggregateUpdate))
                }
                Ok(Some(_)) | Ok(None) => None,
            },
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::LoopHeader
            | CfgNodeKind::Branch { .. }
            | CfgNodeKind::Witness { .. }
            | CfgNodeKind::Constraint { .. }
            | CfgNodeKind::Instantiate { .. }
            | CfgNodeKind::Declaration { .. }
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Assert { .. }
            | CfgNodeKind::DeferredAssert { .. }
            | CfgNodeKind::Log
            | CfgNodeKind::Opaque(_)
            | CfgNodeKind::OpaqueEquality { .. } => None,
        }
    }

    fn failure(&self, path: &AccessPath, error: ShapeError) -> ShapeFailure {
        ShapeFailure { subject: FailureSubject::ValueUse(path.root), span: path.span, error }
    }

    fn assignment_failure(
        &self,
        target: &AccessPath,
        value: ExprId,
        operator: AssignmentOperator,
    ) -> Option<ShapeFailure> {
        let target_rank = match self.target_rank(target) {
            Err(error) => return Some(self.failure(target, error)),
            Ok(rank) => rank?,
        };
        if operator != AssignmentOperator::Assign && target_rank > 0 {
            return Some(self.failure(target, ShapeError::AggregateUpdate));
        }
        let value_rank = self.expression_rank(value, 0)?;
        if target_rank == value_rank {
            return None;
        }
        let mut failure = self.failure(target, ShapeError::AssignmentRank);
        if crate::hir_facts::deferred_scalar_target(self.facts.hir(), target) {
            failure.subject = FailureSubject::ScalarAssignment(value);
            failure.span = self.facts.hir().expression(value)?.span;
        }
        Some(failure)
    }

    fn access_rank(&self, path: &AccessPath) -> Result<Option<usize>, ShapeError> {
        let Some(mut value) = self.arguments.get(&path.root).copied() else { return Ok(None) };
        for step in &path.steps {
            let AccessStep::Index { index, .. } = step else { return Ok(None) };
            let Some(indexed) = self.indexed_argument(value, index)? else { return Ok(None) };
            value = indexed;
        }
        Ok(argument_rank(value))
    }

    fn indexed_argument<'a>(
        &self,
        value: &'a ArgumentValue,
        index: &ArrayIndex,
    ) -> Result<Option<&'a ArgumentValue>, ShapeError> {
        match value {
            ArgumentValue::Scalar(_) | ArgumentValue::Symbolic(ArgumentShape::Scalar) => {
                Err(ShapeError::ScalarIndex)
            }
            ArgumentValue::Array(items) => {
                let Some(index) = self.index_value(index) else { return Ok(None) };
                let index = index.as_bigint().to_usize().ok_or(ShapeError::IndexOutOfBounds)?;
                Ok(Some(items.get(index).ok_or(ShapeError::IndexOutOfBounds)?))
            }
            ArgumentValue::Bus(_)
            | ArgumentValue::Symbolic(
                ArgumentShape::Array | ArgumentShape::Bus | ArgumentShape::Unknown,
            ) => Ok(None),
        }
    }

    fn index_value(&self, index: &ArrayIndex) -> Option<crate::hir_facts::FieldValue> {
        match index {
            ArrayIndex::Constant(value) => self.field.parse(value),
            ArrayIndex::Symbolic(id) => {
                let fact = self.range(*id);
                let Range::Exact(value) = fact.certified()? else { return None };
                Some(value.clone())
            }
        }
    }

    fn expression_rank(&self, id: ExprId, depth: usize) -> Option<usize> {
        if depth >= MAX_ARGUMENT_DEPTH {
            return None;
        }
        let expression = self.facts.hir().expression(id)?;
        match &expression.kind {
            ExprKind::Number(_) => Some(0),
            ExprKind::Array(items) => self.array_rank(items, depth),
            ExprKind::Access(path) => self.expression_access_rank(path),
            ExprKind::Parallel(inner) => self.expression_rank(*inner, depth + 1),
            ExprKind::Ternary { condition, yes, no } => {
                self.ternary_rank(*condition, *yes, *no, depth)
            }
            ExprKind::Unary { .. } | ExprKind::Binary { .. } | ExprKind::Call { .. } => {
                let fact = self.range(id);
                let Range::Exact(_) = fact.certified()? else { return None };
                Some(0)
            }
            ExprKind::Tuple(_) | ExprKind::AnonymousComponent { .. } | ExprKind::Opaque(_) => None,
        }
    }

    fn array_rank(&self, items: &[ExprId], depth: usize) -> Option<usize> {
        let first = self.expression_rank(*items.first()?, depth + 1)?;
        for item in items {
            if self.expression_rank(*item, depth + 1)? != first {
                return None;
            }
        }
        first.checked_add(1)
    }

    fn ternary_rank(
        &self,
        condition: ExprId,
        yes: ExprId,
        no: ExprId,
        depth: usize,
    ) -> Option<usize> {
        if let Some(Range::Exact(value)) = self.range(condition).certified() {
            let selected = if self.field.is_zero(value) { no } else { yes };
            return self.expression_rank(selected, depth + 1);
        }
        let yes = self.expression_rank(yes, depth + 1)?;
        let no = self.expression_rank(no, depth + 1)?;
        (yes == no).then_some(yes)
    }

    fn target_rank(&self, path: &AccessPath) -> Result<Option<usize>, ShapeError> {
        if self.arguments.contains_key(&path.root) {
            return self.access_rank(path);
        }
        Ok(self.declared_rank(path))
    }

    fn expression_access_rank(&self, path: &AccessPath) -> Option<usize> {
        self.target_rank(path).ok()?
    }

    fn declared_rank(&self, path: &AccessPath) -> Option<usize> {
        let symbol = self.facts.hir().symbol(path.terminal)?;
        if !symbol.shape_checked || symbol.bus_type.is_some() {
            return None;
        }
        let mut indices = 0;
        for step in path.steps.iter().rev() {
            match step {
                AccessStep::Index { .. } => indices += 1,
                AccessStep::Port { .. } => break,
                AccessStep::Tag { .. } => return Some(0),
            }
        }
        symbol.rank.checked_sub(indices)
    }
}

fn argument_rank(value: &ArgumentValue) -> Option<usize> {
    match value {
        ArgumentValue::Scalar(_) | ArgumentValue::Symbolic(ArgumentShape::Scalar) => Some(0),
        ArgumentValue::Array(items) => {
            let first = argument_rank(items.first()?)?;
            for item in items {
                if argument_rank(item)? != first {
                    return None;
                }
            }
            first.checked_add(1)
        }
        ArgumentValue::Bus(_)
        | ArgumentValue::Symbolic(
            ArgumentShape::Array | ArgumentShape::Bus | ArgumentShape::Unknown,
        ) => None,
    }
}
