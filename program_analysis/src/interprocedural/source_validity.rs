//! Source validation certificates, distinct from call-context specialization and ancestry.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use parser::hir::{
    BlockId, DefinitionRef, Effect, ExprId, ExprKind, IncompleteReason, IncompleteRegion, Severity,
    SymbolId, SymbolKind,
};
use parser::frontend::{AssignmentOperator, SourceId, Span};

use crate::hir_cfg::{Constraint, CfgNodeKind, Origin};
use crate::hir_facts::{AnalysisFacts, Range};
use crate::interprocedural::{CallOwner, ProjectAnalysis, SummaryBlocker};

/// A checked function or template header bound to this HIR project.
/// Callers cannot construct a validation certificate from a parameter count.
///
/// ```compile_fail
/// use circomspect_program_analysis::interprocedural::ValidatedHeader;
/// fn forge(header: &mut ValidatedHeader) { header.parameter_count = 8; }
/// ```
///
/// Issued by source validation for one definition's name, parameter list, and header coverage.
/// The owned name, span, and parameter count remain bound to that definition's identity.
/// A valid header makes no claim about body completeness or execution.
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

/// A checked header issued after validating the definition's active source regions.
///
/// ```compile_fail
/// use circomspect_program_analysis::interprocedural::{ValidatedDefinition, ValidatedHeader};
/// fn forge(definition: &mut ValidatedDefinition, header: ValidatedHeader) {
///     definition.header = header;
/// }
/// ```
///
/// Issued after header and active-body source checks, including only authorized resolved or
/// dead regions. It stores only the validated header and its definition identity, not the
/// facts or scope used for those checks. It certifies neither successful execution nor
/// completeness of unrelated project definitions.
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

pub(crate) struct SourceQueries<'session, 'hir> {
    pub(super) analysis: &'session ProjectAnalysis<'hir>,
}

impl<'session> SourceQueries<'session, '_> {
    pub(super) fn source_complete(&self) -> bool {
        self.analysis.lifted_project().diagnostics.is_empty()
            && self.analysis.lifted_project().syntax_diagnostics.is_empty()
            && self.analysis.lifted_project().incomplete.is_empty()
    }

    pub(super) fn model_source_complete(
        &self,
        active: DefinitionRef,
        completed: Option<&crate::interprocedural::constructor_readiness::CompletedTemplate>,
    ) -> bool {
        if !self.analysis.lifted_project().syntax_diagnostics.is_empty() {
            return false;
        }
        let connected = self.connected_definitions(active);
        for diagnostic in &self.analysis.lifted_project().diagnostics {
            if !self.other_definition_body_contains(diagnostic.span, &connected) {
                return false;
            }
        }
        for region in &self.analysis.lifted_project().incomplete {
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
        for template in self.analysis.hir().templates() {
            if !completed.contains_checked_definition(DefinitionRef::Template(template.id)) {
                continue;
            }
            let Some(body) = self.analysis.hir().block(template.body) else { continue };
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
            for site in self.analysis.graph().calls_from(CallOwner::Definition(definition)) {
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
        for function in self.analysis.hir().functions() {
            if connected.contains(&DefinitionRef::Function(function.id)) {
                continue;
            }
            let Some(body) = self.analysis.hir().block(function.body) else { continue };
            if SourceScope::from_span(body.span).contains(span) {
                return true;
            }
        }
        for template in self.analysis.hir().templates() {
            if connected.contains(&DefinitionRef::Template(template.id)) {
                continue;
            }
            let Some(body) = self.analysis.hir().block(template.body) else { continue };
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
        let body =
            self.analysis.hir().block(parts.body).ok_or(SummaryBlocker::IncompleteDefinition)?;
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
        if facts.hir().identity() != self.analysis.hir().identity()
            || facts.curve() != self.analysis.curve()
        {
            return Err(SummaryBlocker::WrongContext);
        }
        let header = self.validated_header(definition)?;
        let parts = self.definition_parts(definition)?;
        if self.scope_has_issue_with_facts(SourceScope::from_span(parts.span), facts) {
            return Err(SummaryBlocker::IncompleteDefinition);
        }
        Ok(ValidatedDefinition { header })
    }

    pub(crate) fn has_no_hard_source_issue(&self, definition: DefinitionRef) -> bool {
        if self.validated_header(definition).is_err() {
            return false;
        }
        self.definition_has_hard_source_issue(definition).is_ok_and(|has_issue| !has_issue)
    }

    fn definition_parts(
        &self,
        definition: DefinitionRef,
    ) -> Result<DefinitionParts<'session>, SummaryBlocker> {
        let parts = match definition {
            DefinitionRef::Function(id) => {
                let item =
                    self.analysis.hir().function(id).ok_or(SummaryBlocker::ForeignDefinition)?;
                DefinitionParts {
                    name: &item.name,
                    name_span: item.name_span,
                    span: item.span,
                    body: item.body,
                    parameters: &item.parameters,
                }
            }
            DefinitionRef::Template(id) => {
                let item =
                    self.analysis.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
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
            let Some(symbol) = self.analysis.hir().symbol(*id) else { return false };
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
                .analysis
                .lifted_project()
                .incomplete
                .iter()
                .any(|region| region.span().is_some_and(|span| scope.overlaps(span)))
    }

    fn scope_has_issue_with_facts(&self, scope: SourceScope, facts: &AnalysisFacts<'_>) -> bool {
        self.scope_has_diagnostic(scope)
            || self.analysis.lifted_project().incomplete.iter().any(|region| {
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
        Ok(self.analysis.lifted_project().incomplete.iter().any(|region| {
            region.reason != IncompleteReason::UnknownType
                && region.span().is_some_and(|span| scope.overlaps(span))
        }))
    }

    fn scope_has_diagnostic(&self, scope: SourceScope) -> bool {
        for diagnostic in &self.analysis.lifted_project().syntax_diagnostics {
            if diagnostic.span().is_some_and(|span| scope.overlaps(span)) {
                return true;
            }
        }
        self.analysis.lifted_project().diagnostics.iter().any(|diagnostic| {
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
        let Some(block) = self.analysis.hir().block(origin.block) else { return false };
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
        }) = self
            .analysis
            .hir()
            .block(origin.block)
            .and_then(|block| block.effects.get(origin.effect_index))
        else {
            return false;
        };
        let CfgNodeKind::Constraint(Constraint::Equality {
            left: checked_left,
            right: checked_right,
        }) = &node.kind
        else {
            return false;
        };
        left == checked_left && right == checked_right
    }

    fn resolved_access_region(&self, span: Span, facts: &AnalysisFacts<'_>) -> bool {
        for expression in self.analysis.hir().expressions() {
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
        let Some(effect) = self
            .analysis
            .hir()
            .block(origin.block)
            .and_then(|block| block.effects.get(origin.effect_index))
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
            Effect::Discard { .. }
            | Effect::OpaqueAssignment { .. }
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
                let CfgNodeKind::Constraint(Constraint::Assignment {
                    target: checked,
                    value: checked_value,
                }) = kind
                else {
                    return false;
                };
                checked == target && *checked_value == value
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
}

#[cfg(test)]
mod tests {
    use parser::frontend::{parse_source, LoadedProject, SourceFile, SourceId, Version, VersionPolicy};
    use parser::hir::lift_project;
    use program_structure::utils::constants::Curve;

    use crate::interprocedural::ProjectAnalysis;

    #[test]
    fn temporary_source_views_preserve_definition_borrows() {
        let source = "template T(n){}";
        let policy = VersionPolicy::new(Version::new(2, 2, 3));
        let id = SourceId::new(0);
        let loaded = LoadedProject {
            policy,
            diagnostics: Vec::new(),
            files: vec![SourceFile {
                id,
                path: "source-view.circom".into(),
                text: source.into(),
                outcome: parse_source(id, source, policy),
            }],
        };
        let project = lift_project(&loaded);
        let analysis = ProjectAnalysis::build(&project, Curve::Bn254).unwrap();
        let definition = project.hir.definition("T").unwrap();
        let first = analysis.sources().definition_parts(definition).unwrap();
        let second = {
            let queries = analysis.sources();
            queries.definition_parts(definition).unwrap()
        };
        assert_eq!(first.name, "T");
        assert_eq!(first.parameters.len(), 1);
        assert_eq!(second.name, first.name);
        assert_eq!(second.parameters, first.parameters);
    }
}
