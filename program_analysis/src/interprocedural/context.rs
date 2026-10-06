use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::FlowGraph;
use parser::hir::{
    BlockId, DefinitionRef, Effect, ExprId, ExprKind, HirProject, IncompleteReason,
    IncompleteRegion, LiftedProject, ProjectIdentity, SemanticDiagnostic, Severity, SymbolId,
    SymbolKind,
};
use parser::new_frontend::{AssignmentOperator, SourceId, Span, Version};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::{CfgNodeKind, DefinitionCfg, Origin};
use crate::hir_facts::{
    exact_compile_time, AnalysisFacts, FactBlocker, FieldContext, FieldValue, Range,
};

use super::{
    build_call_graph, CallGraph, CallGraphError, CallOwner, CallSite, CallSiteId, ReachableCall,
};
use crate::interprocedural::cache::SummaryCaches;

const MAX_ARGUMENT_NODES: usize = 4096;
pub(super) const MAX_ARGUMENT_DEPTH: usize = 64;

/// Shape of a compile-time argument before a concrete value is known.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ArgumentShape {
    Scalar,
    Array,
    Bus,
    Unknown,
}

/// A typed compile-time argument. `Symbolic` retains library contexts without a main.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ArgumentValue {
    Scalar(FieldValue),
    Array(Vec<Self>),
    Bus(BTreeMap<String, Self>),
    Symbolic(ArgumentShape),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum CurveKey {
    Bn254,
    Bls12_381,
    Goldilocks,
}

impl From<&Curve> for CurveKey {
    fn from(curve: &Curve) -> Self {
        match curve {
            Curve::Bn254 => Self::Bn254,
            Curve::Bls12_381 => Self::Bls12_381,
            Curve::Goldilocks => Self::Goldilocks,
        }
    }
}

/// A validated specialization key, bound to one HIR, field, version, and definition.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct CallContext {
    project: ProjectIdentity,
    definition: DefinitionRef,
    curve: CurveKey,
    version: Version,
    arguments: Vec<ArgumentValue>,
}

impl CallContext {
    #[must_use]
    pub fn definition(&self) -> DefinitionRef {
        self.definition
    }

    #[must_use]
    pub fn version(&self) -> Version {
        self.version
    }

    #[must_use]
    pub fn arguments(&self) -> &[ArgumentValue] {
        &self.arguments
    }

    pub(crate) fn scalar_seeds(&self, parameters: &[SymbolId]) -> BTreeMap<SymbolId, FieldValue> {
        let mut values = BTreeMap::new();
        for (symbol, argument) in parameters.iter().zip(&self.arguments) {
            match argument {
                ArgumentValue::Scalar(value) => {
                    values.insert(*symbol, value.clone());
                }
                ArgumentValue::Symbolic(_) | ArgumentValue::Array(_) | ArgumentValue::Bus(_) => {}
            }
        }
        values
    }
}

/// Origin of a summary scope. Symbolic roots require universal proof before reporting.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ContextOrigin {
    SymbolicRoot,
    Main(CallSiteId),
    Call(CallSiteId),
}

/// One provider-issued source call in the exact path to a rule scope.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CallPathSite {
    site: CallSiteId,
    owner: CallOwner,
    callee: DefinitionRef,
    span: Span,
}

impl CallPathSite {
    fn from_site(site: &CallSite) -> Result<Self, SummaryBlocker> {
        let callee = site.resolved().ok_or(SummaryBlocker::ForeignCall)?;
        Ok(Self { site: site.id(), owner: site.owner, callee, span: site.span })
    }

    #[must_use]
    pub const fn span(self) -> Span {
        self.span
    }

    #[must_use]
    pub const fn owner(self) -> CallOwner {
        self.owner
    }

    #[must_use]
    pub const fn callee(self) -> DefinitionRef {
        self.callee
    }
}

impl Ord for CallPathSite {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.site, self.owner, self.callee, self.span.source(), self.span.start(), self.span.end())
            .cmp(&(
                other.site,
                other.owner,
                other.callee,
                other.span.source(),
                other.span.start(),
                other.span.end(),
            ))
    }
}

impl PartialOrd for CallPathSite {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// A nonforgeable scope linking a context to a library root or reachable call.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ContextEvidence {
    context: CallContext,
    origin: ContextOrigin,
    call_path: Vec<CallPathSite>,
}

impl ContextEvidence {
    #[must_use]
    pub fn context(&self) -> &CallContext {
        &self.context
    }

    #[must_use]
    pub fn origin(&self) -> ContextOrigin {
        self.origin
    }

    pub(crate) fn call_path(&self) -> &[CallPathSite] {
        &self.call_path
    }
}

/// Why a context cannot be used as certified summary evidence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SummaryBlocker {
    ForeignDefinition,
    IncompleteDefinition,
    ForeignCall,
    WrongContext,
    WrongArity { expected: usize, actual: usize },
    UnprovenArgument(ExprId),
    UnsupportedCallForm,
    LocalFacts(BTreeSet<FactBlocker>),
    UnsupportedContext,
    InvalidAssignment(ExprId),
    InvalidValueUse(SymbolId),
    WrongInstance,
    DuplicateInstance,
    SymbolicInstance,
    MissingInputBinding,
    DuplicateInputBinding,
    WitnessOnlyInput,
    ExternalSummary,
    MissingReturn,
    LocalAnalysis(String),
    RecursiveCycle,
    ContextBudget,
}

/// A checked function or template header bound to this HIR project.
/// Callers cannot construct a validation certificate from a parameter count.
///
/// ```compile_fail
/// use circomspect_program_analysis::interprocedural::ValidatedHeader;
/// fn forge(header: &mut ValidatedHeader) { header.parameter_count = 8; }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidatedHeader {
    definition: DefinitionRef,
    name: String,
    name_span: Span,
    parameter_count: usize,
}

impl ValidatedHeader {
    #[must_use]
    pub fn definition(&self) -> DefinitionRef {
        self.definition
    }

    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub fn name_span(&self) -> Span {
        self.name_span
    }

    #[must_use]
    pub fn parameter_count(&self) -> usize {
        self.parameter_count
    }
}

/// A checked header whose entire definition has no parser, lifting, or semantic errors.
///
/// ```compile_fail
/// use circomspect_program_analysis::interprocedural::{ValidatedDefinition, ValidatedHeader};
/// fn forge(definition: &mut ValidatedDefinition, header: ValidatedHeader) {
///     definition.header = header;
/// }
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidatedDefinition {
    header: ValidatedHeader,
}

impl ValidatedDefinition {
    #[must_use]
    pub fn header(&self) -> &ValidatedHeader {
        &self.header
    }
}

struct DefinitionParts<'a> {
    name: &'a str,
    name_span: Span,
    span: Span,
    body: BlockId,
    parameters: &'a [SymbolId],
}

#[derive(Clone, Copy)]
struct SourceScope {
    source: SourceId,
    start: usize,
    end: usize,
}

impl SourceScope {
    fn from_span(span: Span) -> Self {
        Self { source: span.source(), start: span.start(), end: span.end() }
    }

    fn contains(self, span: Span) -> bool {
        self.source == span.source() && self.start <= span.start() && span.end() <= self.end
    }

    fn overlaps(self, span: Span) -> bool {
        if self.source != span.source() {
            return false;
        }
        if span.start() == span.end() {
            return self.start <= span.start() && span.start() <= self.end;
        }
        span.start() < self.end && self.start < span.end()
    }
}

/// A failed context analysis, retaining a located semantic error when specialization proves one.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AnalyzeEvidenceError {
    Blocked(SummaryBlocker),
    InvalidAssignment { context: Box<CallContext>, diagnostic: Box<SemanticDiagnostic> },
    InvalidValueUse { context: Box<CallContext>, diagnostic: Box<SemanticDiagnostic> },
}

impl AnalyzeEvidenceError {
    #[must_use]
    pub fn diagnostic(&self) -> Option<&SemanticDiagnostic> {
        match self {
            Self::InvalidAssignment { diagnostic, .. }
            | Self::InvalidValueUse { diagnostic, .. } => Some(diagnostic),
            Self::Blocked(_) => None,
        }
    }
}

/// Owns the validated field and graph used to construct summary contexts.
pub struct ProjectSummaries<'a> {
    lifted: &'a LiftedProject,
    field: FieldContext,
    graph: CallGraph,
    pub(super) caches: SummaryCaches,
}

impl<'a> ProjectSummaries<'a> {
    /// Build a provider for one selected compiler curve and the lifted language version.
    ///
    /// # Errors
    /// Returns a graph error if a call site references an invalid HIR identity.
    pub fn build(lifted: &'a LiftedProject, curve: Curve) -> Result<Self, CallGraphError> {
        let graph = build_call_graph(&lifted.hir)?;
        Ok(Self {
            lifted,
            field: FieldContext::for_curve(curve),
            graph,
            caches: SummaryCaches::default(),
        })
    }

    #[must_use]
    pub fn hir(&self) -> &HirProject {
        &self.lifted.hir
    }

    pub(super) fn source_complete(&self) -> bool {
        self.lifted.diagnostics.is_empty()
            && self.lifted.syntax_diagnostics.is_empty()
            && self.lifted.incomplete.is_empty()
    }

    pub(super) fn model_source_complete(
        &self,
        active: DefinitionRef,
        completed: Option<&crate::interprocedural::constructor_readiness::CompletedTemplate>,
    ) -> bool {
        if !self.lifted.syntax_diagnostics.is_empty() {
            return false;
        }
        let connected = self.connected_definitions(active);
        for diagnostic in &self.lifted.diagnostics {
            if !self.other_definition_body_contains(diagnostic.span, &connected) {
                return false;
            }
        }
        for region in &self.lifted.incomplete {
            let scoped = match &region.reason {
                IncompleteReason::Syntax | IncompleteReason::Include => false,
                IncompleteReason::UnknownType => region.span().is_some_and(|span| {
                    self.other_definition_body_contains(span, &connected)
                        || completed
                            .is_some_and(|completed| self.completed_body_contains(span, completed))
                }),
                IncompleteReason::MissingReference(_)
                | IncompleteReason::AmbiguousReference(_)
                | IncompleteReason::WrongKind(_)
                | IncompleteReason::UnknownSymbol(_)
                | IncompleteReason::NonCompileTime
                | IncompleteReason::InvalidAssignment
                | IncompleteReason::Unsupported(_) => region
                    .span()
                    .is_some_and(|span| self.other_definition_body_contains(span, &connected)),
            };
            if !scoped {
                return false;
            }
        }
        true
    }

    fn completed_body_contains(
        &self,
        span: Span,
        completed: &crate::interprocedural::constructor_readiness::CompletedTemplate,
    ) -> bool {
        for template in self.hir().templates() {
            if !completed.contains_checked_definition(DefinitionRef::Template(template.id)) {
                continue;
            }
            let Some(body) = self.hir().block(template.body) else { continue };
            if SourceScope::from_span(body.span).contains(span) {
                return true;
            }
        }
        false
    }

    fn connected_definitions(&self, active: DefinitionRef) -> BTreeSet<DefinitionRef> {
        let mut connected = BTreeSet::new();
        let mut pending = vec![active];
        while let Some(definition) = pending.pop() {
            if !connected.insert(definition) {
                continue;
            }
            for site in self.graph().calls_from(CallOwner::Definition(definition)) {
                if let Some(callee) = site.resolved() {
                    pending.push(callee);
                }
            }
        }
        connected
    }

    fn other_definition_body_contains(
        &self,
        span: Span,
        connected: &BTreeSet<DefinitionRef>,
    ) -> bool {
        for function in self.hir().functions() {
            if connected.contains(&DefinitionRef::Function(function.id)) {
                continue;
            }
            let Some(body) = self.hir().block(function.body) else { continue };
            if SourceScope::from_span(body.span).contains(span) {
                return true;
            }
        }
        for template in self.hir().templates() {
            if connected.contains(&DefinitionRef::Template(template.id)) {
                continue;
            }
            let Some(body) = self.hir().block(template.body) else { continue };
            if SourceScope::from_span(body.span).contains(span) {
                return true;
            }
        }
        false
    }

    pub(crate) fn validated_header(
        &self,
        definition: DefinitionRef,
    ) -> Result<ValidatedHeader, SummaryBlocker> {
        let parts = self.definition_parts(definition)?;
        let body = self.hir().block(parts.body).ok_or(SummaryBlocker::IncompleteDefinition)?;
        let definition_scope = SourceScope::from_span(parts.span);
        if !definition_scope.contains(parts.name_span)
            || !definition_scope.contains(body.span)
            || body.span.start() < parts.name_span.end()
        {
            return Err(SummaryBlocker::IncompleteDefinition);
        }
        let header = SourceScope {
            source: parts.span.source(),
            start: parts.span.start(),
            end: body.span.start(),
        };
        if self.scope_has_issue(header) || !self.parameters_valid(parts.parameters, header) {
            return Err(SummaryBlocker::IncompleteDefinition);
        }
        Ok(ValidatedHeader {
            definition,
            name: parts.name.to_string(),
            name_span: parts.name_span,
            parameter_count: parts.parameters.len(),
        })
    }

    pub(crate) fn validated_definition(
        &self,
        facts: &AnalysisFacts<'_>,
    ) -> Result<ValidatedDefinition, SummaryBlocker> {
        let definition = facts.definition();
        if facts.hir().identity() != self.hir().identity() || facts.curve() != self.curve() {
            return Err(SummaryBlocker::WrongContext);
        }
        let header = self.validated_header(definition)?;
        let parts = self.definition_parts(definition)?;
        if self.scope_has_issue_with_facts(SourceScope::from_span(parts.span), facts) {
            return Err(SummaryBlocker::IncompleteDefinition);
        }
        Ok(ValidatedDefinition { header })
    }

    fn definition_parts(
        &self,
        definition: DefinitionRef,
    ) -> Result<DefinitionParts<'_>, SummaryBlocker> {
        let parts = match definition {
            DefinitionRef::Function(id) => {
                let item = self.hir().function(id).ok_or(SummaryBlocker::ForeignDefinition)?;
                DefinitionParts {
                    name: &item.name,
                    name_span: item.name_span,
                    span: item.span,
                    body: item.body,
                    parameters: &item.parameters,
                }
            }
            DefinitionRef::Template(id) => {
                let item = self.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
                DefinitionParts {
                    name: &item.name,
                    name_span: item.name_span,
                    span: item.span,
                    body: item.body,
                    parameters: &item.parameters,
                }
            }
            DefinitionRef::Bus(_) => return Err(SummaryBlocker::UnsupportedContext),
        };
        Ok(parts)
    }

    fn parameters_valid(&self, parameters: &[SymbolId], header: SourceScope) -> bool {
        let mut names = BTreeSet::new();
        for id in parameters {
            let Some(symbol) = self.hir().symbol(*id) else { return false };
            if symbol.kind != SymbolKind::Parameter
                || !header.contains(symbol.span)
                || !names.insert(symbol.name.as_str())
            {
                return false;
            }
        }
        true
    }

    fn scope_has_issue(&self, scope: SourceScope) -> bool {
        self.scope_has_diagnostic(scope)
            || self
                .lifted
                .incomplete
                .iter()
                .any(|region| region.span().is_some_and(|span| scope.overlaps(span)))
    }

    fn scope_has_issue_with_facts(&self, scope: SourceScope, facts: &AnalysisFacts<'_>) -> bool {
        self.scope_has_diagnostic(scope)
            || self.lifted.incomplete.iter().any(|region| {
                region.span().is_some_and(|span| scope.overlaps(span))
                    && !self.resolved_unknown_region(region, facts)
                    && !self.dead_unknown_region(region, facts)
            })
    }

    pub(super) fn definition_has_hard_source_issue(
        &self,
        definition: DefinitionRef,
    ) -> Result<bool, SummaryBlocker> {
        let parts = self.definition_parts(definition)?;
        let scope = SourceScope::from_span(parts.span);
        if self.scope_has_diagnostic(scope) {
            return Ok(true);
        }
        Ok(self.lifted.incomplete.iter().any(|region| {
            region.reason != IncompleteReason::UnknownType
                && region.span().is_some_and(|span| scope.overlaps(span))
        }))
    }

    fn scope_has_diagnostic(&self, scope: SourceScope) -> bool {
        for diagnostic in &self.lifted.syntax_diagnostics {
            if diagnostic.span().is_some_and(|span| scope.overlaps(span)) {
                return true;
            }
        }
        self.lifted.diagnostics.iter().any(|diagnostic| {
            diagnostic.severity == Severity::Error && scope.overlaps(diagnostic.span)
        })
    }

    fn resolved_unknown_region(
        &self,
        region: &IncompleteRegion,
        facts: &AnalysisFacts<'_>,
    ) -> bool {
        let IncompleteReason::UnknownType = region.reason else { return false };
        let Some(span) = region.span() else { return false };
        if self.resolved_access_region(span, facts) {
            return true;
        }
        for id in facts.cfg().nodes() {
            if self.resolved_assignment_region(*id, span, facts)
                || self.resolved_equality_region(*id, span, facts)
            {
                return true;
            }
        }
        false
    }

    fn dead_unknown_region(&self, region: &IncompleteRegion, facts: &AnalysisFacts<'_>) -> bool {
        let IncompleteReason::UnknownType = region.reason else { return false };
        let Some(span) = region.span() else { return false };
        let Some(effects) = self.unknown_deferred_effects(span, facts) else { return false };
        Self::effect_nodes_are_dead(&effects, facts)
    }

    fn unknown_deferred_effects(
        &self,
        span: Span,
        facts: &AnalysisFacts<'_>,
    ) -> Option<BTreeSet<(BlockId, usize)>> {
        let mut effects = BTreeSet::new();
        for id in facts.cfg().nodes() {
            let node = facts.cfg().node(*id)?;
            let Some(origin) = node.origin else { continue };
            if origin.span == span && self.is_deferred_effect_at(origin, span) {
                effects.insert((origin.block, origin.effect_index));
            }
        }
        if effects.is_empty() {
            None
        } else {
            Some(effects)
        }
    }

    fn is_deferred_effect_at(&self, origin: Origin, span: Span) -> bool {
        let Some(block) = self.hir().block(origin.block) else { return false };
        let Some(Effect::DeferredVariableAssignment { span: effect_span, .. }) =
            block.effects.get(origin.effect_index)
        else {
            return false;
        };
        *effect_span == span
    }

    fn effect_nodes_are_dead(
        effects: &BTreeSet<(BlockId, usize)>,
        facts: &AnalysisFacts<'_>,
    ) -> bool {
        for id in facts.cfg().nodes() {
            let Some(node) = facts.cfg().node(*id) else { return false };
            let Some(origin) = node.origin else { continue };
            if effects.contains(&(origin.block, origin.effect_index))
                && !facts.certified_dead_node(*id)
            {
                return false;
            }
        }
        true
    }

    fn resolved_equality_region(
        &self,
        id: abstract_interpretation::graph::NodeId,
        span: Span,
        facts: &AnalysisFacts<'_>,
    ) -> bool {
        let Some(node) = facts.cfg().node(id) else { return false };
        let Some(origin) = node.origin else { return false };
        if origin.span != span || facts.reachable_node(id).certified() != Some(&true) {
            return false;
        }
        let Some(Effect::OpaqueEquality {
            left, right, reason: IncompleteReason::UnknownType, ..
        }) =
            self.hir().block(origin.block).and_then(|block| block.effects.get(origin.effect_index))
        else {
            return false;
        };
        let CfgNodeKind::Constraint {
            target: None,
            left: checked_left,
            right: Some(checked_right),
        } = &node.kind
        else {
            return false;
        };
        left == checked_left && right == checked_right
    }

    fn resolved_access_region(&self, span: Span, facts: &AnalysisFacts<'_>) -> bool {
        for expression in self.hir().expressions() {
            if expression.span != span {
                continue;
            }
            let ExprKind::Access(path) = &expression.kind else { continue };
            if !path.steps.is_empty() {
                continue;
            }
            if facts.reachable_expression(expression.id).certified() != Some(&true) {
                continue;
            }
            if let Some(Range::Exact(_)) = facts.range(expression.id).certified() {
                return true;
            }
        }
        false
    }

    fn resolved_assignment_region(
        &self,
        id: abstract_interpretation::graph::NodeId,
        span: Span,
        facts: &AnalysisFacts<'_>,
    ) -> bool {
        let Some(node) = facts.cfg().node(id) else { return false };
        let Some(origin) = node.origin else { return false };
        if origin.span != span || facts.reachable_node(id).certified() != Some(&true) {
            return false;
        }
        let Some(effect) =
            self.hir().block(origin.block).and_then(|block| block.effects.get(origin.effect_index))
        else {
            return false;
        };
        match effect {
            Effect::DeferredVariableAssignment { target, value, operator, .. } => {
                let CfgNodeKind::DeferredAssignment {
                    target: checked,
                    value: checked_value,
                    operator: checked_operator,
                } = &node.kind
                else {
                    return false;
                };
                target == checked
                    && value == checked_value
                    && operator == checked_operator
                    && facts.resolved_deferred_assignment(id)
            }
            Effect::OpaqueAssignment { target, value, operator, reason, .. }
                if *reason == IncompleteReason::UnknownType =>
            {
                Self::matches_checked_assignment(&node.kind, target, *value, *operator)
            }
            Effect::OpaqueAssignment { .. }
            | Effect::Declaration { .. }
            | Effect::VariableAssignment { .. }
            | Effect::ComponentInstantiation { .. }
            | Effect::WitnessAssignment { .. }
            | Effect::ConstraintAssignment { .. }
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
            | Effect::Block(_)
            | Effect::Opaque { .. } => false,
        }
    }

    fn matches_checked_assignment(
        kind: &CfgNodeKind,
        target: &parser::hir::AccessPath,
        value: ExprId,
        operator: AssignmentOperator,
    ) -> bool {
        match operator {
            AssignmentOperator::Assign => {
                let CfgNodeKind::Assignment {
                    target: checked,
                    value: checked_value,
                    operator: checked_operator,
                } = kind
                else {
                    return false;
                };
                checked == target && *checked_value == value && *checked_operator == operator
            }
            AssignmentOperator::Witness | AssignmentOperator::ReverseWitness => {
                let CfgNodeKind::Witness { target: checked, value: checked_value } = kind else {
                    return false;
                };
                checked == target && *checked_value == value
            }
            AssignmentOperator::Constraint | AssignmentOperator::ReverseConstraint => {
                let CfgNodeKind::Constraint { target: Some(checked), left, right: None } = kind
                else {
                    return false;
                };
                checked == target && *left == value
            }
            AssignmentOperator::Add
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
            | AssignmentOperator::BitXor => false,
        }
    }

    #[must_use]
    pub fn graph(&self) -> &CallGraph {
        &self.graph
    }

    #[must_use]
    pub fn curve(&self) -> &Curve {
        self.field.curve()
    }

    pub(crate) fn field_context(&self) -> &FieldContext {
        &self.field
    }

    /// Construct a key only when the definition and parameter count belong to this HIR.
    ///
    /// # Errors
    /// Returns a blocker for a foreign definition or a mismatched argument count.
    pub fn context_for(
        &self,
        definition: DefinitionRef,
        arguments: Vec<ArgumentValue>,
    ) -> Result<CallContext, SummaryBlocker> {
        let expected = self.parameter_count(definition).ok_or(SummaryBlocker::ForeignDefinition)?;
        if arguments.len() != expected {
            return Err(SummaryBlocker::WrongArity { expected, actual: arguments.len() });
        }
        let arguments = arguments.into_iter().map(|value| self.canonicalize(value)).collect();
        Ok(CallContext {
            project: self.lifted.hir.identity(),
            definition,
            curve: self.field.curve().into(),
            version: self.lifted.version,
            arguments,
        })
    }

    /// Create the universal library-root context without requiring a `main` instance.
    ///
    /// # Errors
    /// Returns a blocker when the definition does not belong to this project.
    pub fn symbolic_context_for(
        &self,
        definition: DefinitionRef,
    ) -> Result<CallContext, SummaryBlocker> {
        let count = self.parameter_count(definition).ok_or(SummaryBlocker::ForeignDefinition)?;
        self.context_for(definition, vec![ArgumentValue::Symbolic(ArgumentShape::Unknown); count])
    }

    /// Validate that a specialization key belongs to this provider.
    ///
    /// # Errors
    /// Returns a blocker for a different project, curve, version, definition, or arity.
    pub fn check_context(&self, context: &CallContext) -> Result<(), SummaryBlocker> {
        if context.project != self.lifted.hir.identity()
            || context.curve != self.field.curve().into()
            || context.version != self.lifted.version
        {
            return Err(SummaryBlocker::WrongContext);
        }
        let expected =
            self.parameter_count(context.definition).ok_or(SummaryBlocker::ForeignDefinition)?;
        if context.arguments.len() != expected {
            return Err(SummaryBlocker::WrongArity { expected, actual: context.arguments.len() });
        }
        Ok(())
    }

    /// A library definition is a scope even without a `main` instantiation.
    /// A finding still needs a predicate proved for all symbolic values.
    ///
    /// # Errors
    /// Returns a blocker when the definition does not belong to this project.
    pub fn symbolic_root(
        &self,
        definition: DefinitionRef,
    ) -> Result<ContextEvidence, SummaryBlocker> {
        Ok(ContextEvidence {
            context: self.symbolic_context_for(definition)?,
            origin: ContextOrigin::SymbolicRoot,
            call_path: Vec::new(),
        })
    }

    /// Bind a checked `main` call to independently proved compile-time arguments.
    ///
    /// # Errors
    /// Returns a blocker for a foreign main call or arguments that cannot be proved exact.
    pub fn main_evidence(
        &self,
        call: &ReachableCall<'_>,
    ) -> Result<ContextEvidence, SummaryBlocker> {
        let site = call.site();
        let CallOwner::Main(index) = site.owner else { return Err(SummaryBlocker::ForeignCall) };
        if self.graph.site(site.id()) != Some(site) {
            return Err(SummaryBlocker::ForeignCall);
        }
        let main = self.hir().mains().get(index).ok_or(SummaryBlocker::ForeignCall)?;
        if site.target != main.target || site.span != main.span {
            return Err(SummaryBlocker::ForeignCall);
        }
        let arguments = self.exact_main_arguments(&main.arguments)?;
        let context = self.context_for(call.callee(), arguments)?;
        Ok(ContextEvidence {
            context,
            origin: ContextOrigin::Main(site.id()),
            call_path: vec![CallPathSite::from_site(site)?],
        })
    }

    /// Bind a checked reachable definition call to certified exact argument values.
    ///
    /// # Errors
    /// Returns a blocker for mismatched facts, an invalid call scope, or unproved arguments.
    pub fn call_evidence(
        &self,
        call: &ReachableCall<'_>,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
    ) -> Result<ContextEvidence, SummaryBlocker> {
        if self.hir().identity() != facts.hir().identity() || self.curve() != facts.curve() {
            return Err(SummaryBlocker::ForeignCall);
        }
        self.check_facts_for_evidence(facts, caller)?;
        let context = self.call_context(call, facts)?;
        self.check_call_execution_scope(facts, caller)?;
        self.extend_call_evidence(call.site(), context, caller)
    }

    /// Bind a source-matched provisional function call after exact return refinement.
    ///
    /// The raw graph remains provisional. This certificate additionally requires a
    /// provider-owned exact call result, certified reachability, exact arguments,
    /// and local facts bound to the supplied caller ancestry.
    ///
    /// # Errors
    /// Returns a typed blocker when any required scope, call, or value proof is absent.
    pub fn refined_function_call_evidence(
        &self,
        site: CallSiteId,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
    ) -> Result<ContextEvidence, SummaryBlocker> {
        self.check_facts_for_evidence(facts, caller)?;
        let site = self.graph.site(site).ok_or(SummaryBlocker::ForeignCall)?;
        let context = self.exact_site_context(site, facts)?;
        self.check_call_execution_scope(facts, caller)?;
        self.extend_call_evidence(site, context, caller)
    }

    fn extend_call_evidence(
        &self,
        site: &CallSite,
        context: CallContext,
        caller: &ContextEvidence,
    ) -> Result<ContextEvidence, SummaryBlocker> {
        let mut call_path = caller.call_path.clone();
        call_path.push(CallPathSite::from_site(site)?);
        let evidence =
            ContextEvidence { context, origin: ContextOrigin::Call(site.id()), call_path };
        self.check_evidence(&evidence)?;
        Ok(evidence)
    }

    pub(super) fn call_context(
        &self,
        call: &ReachableCall<'_>,
        facts: &AnalysisFacts<'_>,
    ) -> Result<CallContext, SummaryBlocker> {
        let site = call.site();
        if self.hir().identity() != facts.hir().identity()
            || self.curve() != facts.curve()
            || self.graph.site(site.id()) != Some(site)
        {
            return Err(SummaryBlocker::ForeignCall);
        }
        let CallOwner::Definition(owner) = site.owner else {
            return Err(SummaryBlocker::ForeignCall);
        };
        if owner != facts.definition() {
            return Err(SummaryBlocker::ForeignCall);
        }
        let expression = site.expression.ok_or(SummaryBlocker::UnsupportedCallForm)?;
        let reachable = facts.reachable_expression(expression);
        match reachable.certified() {
            Some(true) => {}
            Some(false) => return Err(SummaryBlocker::ForeignCall),
            None => {
                return Err(SummaryBlocker::LocalFacts(
                    reachable.unavailable().cloned().unwrap_or_default(),
                ));
            }
        }
        let Some(expr) = self.hir().expression(expression) else {
            return Err(SummaryBlocker::ForeignCall);
        };
        let (ExprKind::Call { arguments, .. } | ExprKind::AnonymousComponent { arguments, .. }) =
            &expr.kind
        else {
            return Err(SummaryBlocker::UnsupportedCallForm);
        };
        let arguments = self.exact_call_arguments(arguments, facts)?;
        self.context_for(call.callee(), arguments)
    }

    /// Revalidate a scope before a rule combines it with local facts.
    ///
    /// # Errors
    /// Returns a blocker for an invalid context, root origin, or source call path.
    pub fn check_evidence(&self, evidence: &ContextEvidence) -> Result<(), SummaryBlocker> {
        self.check_context(&evidence.context)?;
        match evidence.origin {
            ContextOrigin::SymbolicRoot => {
                if !evidence
                    .context
                    .arguments
                    .iter()
                    .all(|value| matches!(value, ArgumentValue::Symbolic(ArgumentShape::Unknown)))
                {
                    return Err(SummaryBlocker::WrongContext);
                }
            }
            ContextOrigin::Main(_) | ContextOrigin::Call(_) => {}
        }
        self.check_call_path(evidence)
    }

    fn check_call_path(&self, evidence: &ContextEvidence) -> Result<(), SummaryBlocker> {
        Self::check_path_origin(evidence)?;
        if evidence.call_path.is_empty() {
            return Ok(());
        }
        let mut previous = None;
        for step in &evidence.call_path {
            previous = Some(self.check_path_site(*step, previous)?);
        }
        if previous != Some(evidence.context.definition) {
            return Err(SummaryBlocker::ForeignCall);
        }
        Ok(())
    }

    fn check_path_origin(evidence: &ContextEvidence) -> Result<(), SummaryBlocker> {
        match evidence.origin {
            ContextOrigin::SymbolicRoot => {
                if evidence.call_path.is_empty() {
                    Ok(())
                } else {
                    Err(SummaryBlocker::WrongContext)
                }
            }
            ContextOrigin::Main(id) => Self::check_main_path(id, &evidence.call_path),
            ContextOrigin::Call(id) => {
                if evidence.call_path.last().is_some_and(|site| site.site == id) {
                    Ok(())
                } else {
                    Err(SummaryBlocker::ForeignCall)
                }
            }
        }
    }

    fn check_main_path(id: CallSiteId, path: &[CallPathSite]) -> Result<(), SummaryBlocker> {
        let [site] = path else { return Err(SummaryBlocker::ForeignCall) };
        if site.site != id {
            return Err(SummaryBlocker::ForeignCall);
        }
        let CallOwner::Main(_) = site.owner else { return Err(SummaryBlocker::ForeignCall) };
        Ok(())
    }

    fn check_path_site(
        &self,
        step: CallPathSite,
        previous: Option<DefinitionRef>,
    ) -> Result<DefinitionRef, SummaryBlocker> {
        let site = self.graph.site(step.site).ok_or(SummaryBlocker::ForeignCall)?;
        if CallPathSite::from_site(site)? != step {
            return Err(SummaryBlocker::ForeignCall);
        }
        if let Some(previous) = previous {
            if step.owner != CallOwner::Definition(previous) {
                return Err(SummaryBlocker::ForeignCall);
            }
        }
        Ok(step.callee)
    }

    /// Analyze one definition under a validated source scope and bind the result to it.
    ///
    /// # Errors
    /// Returns a blocker for invalid scope or unavailable facts, or a located shape error.
    pub fn analyze_for_evidence<'b>(
        &'b self,
        cfg: &'b DefinitionCfg,
        evidence: &ContextEvidence,
        budget: Option<usize>,
    ) -> Result<AnalysisFacts<'b>, AnalyzeEvidenceError> {
        self.check_evidence(evidence).map_err(AnalyzeEvidenceError::Blocked)?;
        if cfg.definition() != evidence.context.definition {
            return Err(AnalyzeEvidenceError::Blocked(SummaryBlocker::WrongContext));
        }
        let parameters = self
            .parameters(cfg.definition())
            .ok_or(AnalyzeEvidenceError::Blocked(SummaryBlocker::ForeignDefinition))?;
        let seeds = evidence.context.scalar_seeds(parameters);
        let mut facts = self
            .refined_facts(evidence.context(), &seeds, budget)
            .map_err(AnalyzeEvidenceError::Blocked)?;
        if let Some(failure) = self.invalid_value_use(parameters, evidence.context(), &facts) {
            return Err(failure.into_analysis_error(evidence.context()));
        }
        facts.bind_evidence(evidence.clone());
        Ok(facts)
    }

    /// Check that local facts were computed under this exact certified source scope.
    ///
    /// # Errors
    /// Returns a blocker unless facts belong to this exact project, field, and scope.
    pub fn check_facts_for_evidence(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.check_evidence(evidence)?;
        if facts.hir().identity() != self.hir().identity()
            || facts.curve() != self.curve()
            || facts.definition() != evidence.context.definition
            || !facts.matches_evidence(evidence)
        {
            return Err(SummaryBlocker::WrongContext);
        }
        Ok(())
    }

    fn exact_main_arguments(
        &self,
        arguments: &[ExprId],
    ) -> Result<Vec<ArgumentValue>, SummaryBlocker> {
        let mut values = Vec::with_capacity(arguments.len());
        let mut remaining = MAX_ARGUMENT_NODES;
        for expression in arguments {
            values.push(self.exact_argument(*expression, None, 0, &mut remaining)?);
        }
        Ok(values)
    }

    pub(super) fn exact_call_arguments(
        &self,
        arguments: &[ExprId],
        facts: &AnalysisFacts<'_>,
    ) -> Result<Vec<ArgumentValue>, SummaryBlocker> {
        let mut values = Vec::with_capacity(arguments.len());
        let mut remaining = MAX_ARGUMENT_NODES;
        for expression in arguments {
            values.push(self.exact_argument(*expression, Some(facts), 0, &mut remaining)?);
        }
        Ok(values)
    }

    fn exact_argument(
        &self,
        expression: ExprId,
        facts: Option<&AnalysisFacts<'_>>,
        depth: usize,
        remaining: &mut usize,
    ) -> Result<ArgumentValue, SummaryBlocker> {
        if depth >= MAX_ARGUMENT_DEPTH || *remaining == 0 {
            return Err(SummaryBlocker::ContextBudget);
        }
        *remaining -= 1;
        let expression_node =
            self.hir().expression(expression).ok_or(SummaryBlocker::ForeignCall)?;
        if let ExprKind::Array(items) = &expression_node.kind {
            let mut values = Vec::with_capacity(items.len());
            for item in items {
                values.push(self.exact_argument(*item, facts, depth + 1, remaining)?);
            }
            return Ok(ArgumentValue::Array(values));
        }
        let Some(facts) = facts else {
            let value = exact_compile_time(self.hir(), &self.field, expression)
                .ok_or(SummaryBlocker::UnprovenArgument(expression))?;
            return Ok(ArgumentValue::Scalar(value));
        };
        let range = facts.range(expression);
        let Some(range) = range.certified() else {
            return Err(SummaryBlocker::LocalFacts(
                range.unavailable().cloned().unwrap_or_default(),
            ));
        };
        let Range::Exact(value) = range else {
            return Err(SummaryBlocker::UnprovenArgument(expression));
        };
        Ok(ArgumentValue::Scalar(value.clone()))
    }

    fn parameter_count(&self, definition: DefinitionRef) -> Option<usize> {
        match definition {
            DefinitionRef::Function(id) => {
                self.hir().function(id).map(|item| item.parameters.len())
            }
            DefinitionRef::Template(id) => {
                self.hir().template(id).map(|item| item.parameters.len())
            }
            DefinitionRef::Bus(id) => self.hir().bus(id).map(|item| item.parameters.len()),
        }
    }

    fn parameters(&self, definition: DefinitionRef) -> Option<&[SymbolId]> {
        match definition {
            DefinitionRef::Function(id) => {
                self.hir().function(id).map(|item| item.parameters.as_slice())
            }
            DefinitionRef::Template(id) => {
                self.hir().template(id).map(|item| item.parameters.as_slice())
            }
            DefinitionRef::Bus(id) => self.hir().bus(id).map(|item| item.parameters.as_slice()),
        }
    }

    fn canonicalize(&self, value: ArgumentValue) -> ArgumentValue {
        match value {
            ArgumentValue::Scalar(value) => {
                ArgumentValue::Scalar(self.field.canonical(value.as_bigint().clone()))
            }
            ArgumentValue::Array(items) => ArgumentValue::Array(
                items.into_iter().map(|item| self.canonicalize(item)).collect(),
            ),
            ArgumentValue::Bus(fields) => ArgumentValue::Bus(
                fields.into_iter().map(|(name, item)| (name, self.canonicalize(item))).collect(),
            ),
            ArgumentValue::Symbolic(shape) => ArgumentValue::Symbolic(shape),
        }
    }
}

#[cfg(test)]
mod tests {
    use parser::hir::{lift_project, DefinitionRef, SemanticCode, Severity};
    use parser::new_frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::build_cfg;
    use crate::interprocedural::{
        ArgumentValue, CallOwner, CallReachability, ProjectSummaries, SummaryBlocker,
    };

    #[test]
    fn a_symbolic_scope_cannot_borrow_a_reachable_origin() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-summary-binding-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        std::fs::write(&source, "template T(n){signal output y;y<==n;} component main=T(1);")
            .unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let DefinitionRef::Template(template) = lifted.hir.definition("T").unwrap() else {
            panic!("template T")
        };
        let site = provider.graph.calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph.reachable_main_call(site.id(), provider.hir())
        else {
            panic!("main call")
        };
        let evidence = provider.main_evidence(&call).unwrap();
        let cfg = build_cfg(provider.hir(), DefinitionRef::Template(template)).unwrap();
        let symbolic = provider.symbolic_root(DefinitionRef::Template(template)).unwrap();
        let wrong = provider.analyze_for_evidence(&cfg, &symbolic, None).unwrap();
        assert_eq!(
            provider.check_facts_for_evidence(&wrong, &evidence),
            Err(SummaryBlocker::WrongContext)
        );
    }

    #[test]
    fn invalid_deferred_write_cannot_bind_complete_array_context_facts() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-array-binding-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        let source_text =
            "template T(n){var x=n;x=1;signal output y;y<==1;} component main=T([1,2]);";
        std::fs::write(&source, source_text).unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("T").unwrap();
        let main = provider.graph.calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph.reachable_main_call(main.id(), provider.hir())
        else {
            panic!("main call")
        };
        let evidence = provider.main_evidence(&call).unwrap();
        assert_eq!(
            evidence.context().arguments(),
            [ArgumentValue::Array(vec![
                ArgumentValue::Scalar(provider.field.canonical(1.into())),
                ArgumentValue::Scalar(provider.field.canonical(2.into())),
            ])]
        );
        let cfg = build_cfg(provider.hir(), definition).unwrap();
        let error = provider.analyze_for_evidence(&cfg, &evidence, None).err().unwrap();
        let super::AnalyzeEvidenceError::InvalidAssignment { context, diagnostic } = error else {
            panic!("aggregate assignment must emit a located error")
        };
        assert_eq!(*context, *evidence.context());
        assert_eq!(diagnostic.code, SemanticCode::InvalidAssignment);
        assert_eq!(diagnostic.code.as_str(), "T2000");
        assert_eq!(diagnostic.severity, Severity::Error);
        assert_eq!(&source_text[diagnostic.span.start()..diagnostic.span.end()], "n");
    }

    #[test]
    fn aggregate_argument_depth_budget_abstains_without_a_context() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-array-depth-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        let nested = format!(
            "{}1{}",
            "[".repeat(super::MAX_ARGUMENT_DEPTH),
            "]".repeat(super::MAX_ARGUMENT_DEPTH)
        );
        std::fs::write(&source, format!("template T(n){{}} component main=T({nested});")).unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let site = provider.graph.calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph.reachable_main_call(site.id(), provider.hir())
        else {
            panic!("main call must be reachable")
        };
        assert_eq!(provider.main_evidence(&call), Err(SummaryBlocker::ContextBudget));
    }
}
