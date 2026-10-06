//! Output-use proofs scoped to a validated, closed `main` root.

use std::collections::BTreeSet;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use parser::hir::{
    AccessPath, AccessStep, ArrayIndex, BusTarget, CallTarget, ControlGuard, DefinitionRef, ExprId,
    ExprKind, PortSchema, Symbol, SymbolId, SymbolKind,
};
use parser::new_frontend::{AssignmentOperator, PortDirection, Span};

use crate::hir_cfg::{build_cfg, CfgNodeKind, DefinitionCfg, Origin};
use crate::hir_facts::{AccessHandle, AnalysisFacts, FieldContext, Range};
use crate::interprocedural::component::LocalOutputUse;
use crate::interprocedural::summary::{certified, is_proven_nonzero};
use crate::interprocedural::{
    AppliedComponentPort, CallOwner, CallSiteId, ContextEvidence, ContextOrigin, ProjectSummaries,
    SummaryBlocker, SummaryFact,
};

/// Project-root observation of one exact output path.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProjectOutputStatus {
    Read,
    Unused,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum OutputTarget {
    Component(Box<AppliedComponentPort>),
    Exported(Box<AccessHandle>),
}

#[derive(Clone, Copy)]
enum MainSourceScope {
    WholeProject,
    ModelDefinitions,
}

/// A project-wide output-use result for one bounded main-rooted instance chain.
///
/// Only the provider can construct this after validating main, project
/// completeness, and an exact output path. `Unused` never describes a library
/// root or an exported main port.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectOutputUse {
    main: ContextEvidence,
    target: OutputTarget,
    status: ProjectOutputStatus,
    source_reads: Vec<Origin>,
    source_span: Span,
    instance_path: Vec<ProjectInstanceStep>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectInstanceStep {
    site: CallSiteId,
    target: AccessPath,
    indices: Vec<usize>,
    callee: ContextEvidence,
}

impl ProjectInstanceStep {
    pub(super) fn new(
        site: CallSiteId,
        target: AccessPath,
        indices: Vec<usize>,
        callee: ContextEvidence,
    ) -> Self {
        Self { site, target, indices, callee }
    }

    #[must_use]
    pub fn site(&self) -> CallSiteId {
        self.site
    }

    #[must_use]
    pub fn indices(&self) -> &[usize] {
        &self.indices
    }

    /// Exact source component target for this step of the checked instance path.
    #[must_use]
    pub fn target(&self) -> &AccessPath {
        &self.target
    }

    #[must_use]
    pub fn callee_evidence(&self) -> &ContextEvidence {
        &self.callee
    }
}

pub(super) struct ProjectOutputEvidence {
    pub reads: Vec<Origin>,
    pub span: Span,
    pub path: Vec<ProjectInstanceStep>,
}

impl ProjectOutputUse {
    #[must_use]
    pub fn status(&self) -> ProjectOutputStatus {
        self.status
    }

    #[must_use]
    pub fn handle(&self) -> &AccessHandle {
        match &self.target {
            OutputTarget::Component(applied) => applied.handle(),
            OutputTarget::Exported(handle) => handle,
        }
    }

    #[must_use]
    pub fn main_evidence(&self) -> &ContextEvidence {
        &self.main
    }

    #[must_use]
    pub fn source_reads(&self) -> &[Origin] {
        &self.source_reads
    }

    #[must_use]
    pub fn source_span(&self) -> Span {
        self.source_span
    }

    #[must_use]
    pub fn instance_depth(&self) -> usize {
        self.instance_path.len()
    }

    #[must_use]
    pub fn instance_path(&self) -> &[ProjectInstanceStep] {
        &self.instance_path
    }

    #[must_use]
    pub fn output_indices(&self) -> Option<&[usize]> {
        let OutputTarget::Component(applied) = &self.target else { return None };
        Some(applied.port_summary().indices())
    }

    pub(super) fn component(
        main: ContextEvidence,
        applied: AppliedComponentPort,
        status: ProjectOutputStatus,
        evidence: ProjectOutputEvidence,
    ) -> Self {
        Self {
            main,
            target: OutputTarget::Component(Box::new(applied)),
            status,
            source_reads: evidence.reads,
            source_span: evidence.span,
            instance_path: evidence.path,
        }
    }
}

impl ProjectSummaries<'_> {
    pub(super) fn check_parent_components_complete(
        &self,
        facts: &AnalysisFacts<'_>,
    ) -> Result<(), SummaryBlocker> {
        for component in self.hir().components() {
            if !facts.cfg().owns_symbol(component.symbol) {
                continue;
            }
            Self::check_component_complete(facts, component)?;
        }
        Ok(())
    }

    fn check_component_complete(
        facts: &AnalysisFacts<'_>,
        component: &parser::hir::Component,
    ) -> Result<(), SummaryBlocker> {
        let bounds =
            facts.component_bounds(component.id).map_err(|_| SummaryBlocker::UnsupportedContext)?;
        let expected = match bounds.as_slice() {
            [] => 1,
            [bound] => *bound,
            [_, _, ..] => return Err(SummaryBlocker::UnsupportedContext),
        };
        let mut instantiated = BTreeSet::new();
        for id in facts.cfg().nodes() {
            let Some(CfgNodeKind::Instantiate { target, .. }) =
                facts.cfg().node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            if target.root != component.symbol || !*certified(&facts.reachable_node(*id))? {
                continue;
            }
            if !*certified(&facts.must_execute(*id))? {
                return Err(SummaryBlocker::UnsupportedContext);
            }
            let index = Self::exact_instance_index(&target.steps, bounds.as_slice())?;
            if !instantiated.insert(index) {
                return Err(SummaryBlocker::UnsupportedContext);
            }
        }
        if instantiated.len() != expected {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        Ok(())
    }

    fn exact_instance_index(
        steps: &[AccessStep],
        bounds: &[usize],
    ) -> Result<usize, SummaryBlocker> {
        match (steps, bounds) {
            ([], []) => Ok(0),
            ([AccessStep::Index { index: ArrayIndex::Constant(index), .. }], [bound]) => {
                let index = index.parse().map_err(|_| SummaryBlocker::UnsupportedContext)?;
                if index < *bound {
                    Ok(index)
                } else {
                    Err(SummaryBlocker::UnsupportedContext)
                }
            }
            _ => Err(SummaryBlocker::UnsupportedContext),
        }
    }

    pub(super) fn check_template_execution(
        &self,
        cfg: &DefinitionCfg,
        facts: &AnalysisFacts<'_>,
    ) -> Result<(), SummaryBlocker> {
        let field = FieldContext::for_curve(self.curve().clone());
        for id in cfg.nodes() {
            let node = cfg.node(*id).ok_or(SummaryBlocker::ExternalSummary)?;
            if !*certified(&facts.reachable_node(*id))? {
                continue;
            }
            if self.template_node_may_fail(*id, &node.kind, facts, &field) {
                return Err(SummaryBlocker::UnsupportedContext);
            }
        }
        Ok(())
    }

    fn template_node_may_fail(
        &self,
        id: NodeId,
        kind: &CfgNodeKind,
        facts: &AnalysisFacts<'_>,
        field: &FieldContext,
    ) -> bool {
        match kind {
            CfgNodeKind::Assert { condition } | CfgNodeKind::DeferredAssert { condition } => {
                !is_proven_nonzero(facts.range(*condition).certified(), field)
            }
            CfgNodeKind::Evaluate(expression) => {
                self.template_expression_may_fail(*expression, facts.cfg(), facts, field)
            }
            CfgNodeKind::Witness { target, .. }
            | CfgNodeKind::Instantiate { target, .. }
            | CfgNodeKind::Update { target, .. } => facts.checked_access_bounds(target).is_err(),
            CfgNodeKind::Constraint { target, .. } => {
                target.as_ref().is_some_and(|target| facts.checked_access_bounds(target).is_err())
            }
            CfgNodeKind::Assignment { target, operator, .. } => {
                *operator != AssignmentOperator::Assign
                    || facts.checked_access_bounds(target).is_err()
            }
            CfgNodeKind::DeferredAssignment { target, operator, .. } => {
                *operator != AssignmentOperator::Assign
                    || !facts.resolved_deferred_assignment(id)
                    || facts.checked_access_bounds(target).is_err()
            }
            CfgNodeKind::Branch { condition, guard } => match guard {
                ControlGuard::CheckedCompileTime => {
                    let range = facts.range(*condition);
                    let Some(Range::Exact(_)) = range.certified() else { return true };
                    false
                }
                ControlGuard::DeferredScalar | ControlGuard::WitnessOnly => true,
            },
            CfgNodeKind::Opaque(_)
            | CfgNodeKind::OpaqueAssignment { .. }
            | CfgNodeKind::OpaqueEquality { .. }
            | CfgNodeKind::LoopHeader => true,
            CfgNodeKind::Declaration { symbol } => self.declaration_may_fail(*symbol, facts),
            CfgNodeKind::Entry | CfgNodeKind::Exit | CfgNodeKind::Return(_) | CfgNodeKind::Log => {
                false
            }
        }
    }

    pub(super) fn declaration_may_fail(&self, id: SymbolId, facts: &AnalysisFacts<'_>) -> bool {
        let Some(symbol) = self.hir().symbol(id) else { return true };
        if facts.checked_symbol_dimensions(id).is_err() {
            return true;
        }
        if let SymbolKind::Bus = symbol.kind {
            return self.bus_schema_may_fail(symbol);
        }
        false
    }

    fn bus_schema_may_fail(&self, symbol: &Symbol) -> bool {
        let Some(BusTarget::Bus(id)) = &symbol.bus_type else { return true };
        let Some(bus) = self.hir().bus(*id) else { return true };
        if !bus.parameters.is_empty() || !symbol.bus_arguments.is_empty() {
            return true;
        }
        let definition = DefinitionRef::Bus(*id);
        let Ok(cfg) = build_cfg(self.hir(), definition) else { return true };
        let Ok(evidence) = self.symbolic_root(definition) else { return true };
        let Ok(facts) = self.analyze_for_evidence(&cfg, &evidence, None) else { return true };
        let field = FieldContext::for_curve(self.curve().clone());
        for id in cfg.nodes() {
            let Some(node) = cfg.node(*id) else { return true };
            if facts.reachable_node(*id).certified() != Some(&true) {
                return true;
            }
            match node.kind {
                CfgNodeKind::Entry | CfgNodeKind::Exit => {}
                CfgNodeKind::Evaluate(expression) => {
                    if self.expression_may_fail(expression, &facts, &field) {
                        return true;
                    }
                }
                CfgNodeKind::Declaration { symbol } => {
                    let Some(field) = self.hir().symbol(symbol) else { return true };
                    if field.kind == SymbolKind::Bus
                        || facts.checked_symbol_dimensions(symbol).is_err()
                    {
                        return true;
                    }
                }
                _ => return true,
            }
        }
        false
    }

    fn template_expression_may_fail(
        &self,
        id: ExprId,
        cfg: &DefinitionCfg,
        facts: &AnalysisFacts<'_>,
        field: &FieldContext,
    ) -> bool {
        let Some(expression) = self.hir().expression(id) else { return true };
        if let ExprKind::Call { target: CallTarget::Template(_), .. } = &expression.kind {
            return !cfg.nodes().iter().any(|node| {
                if let Some(CfgNodeKind::Instantiate { value, .. }) =
                    cfg.node(*node).map(|node| &node.kind)
                {
                    *value == id
                } else {
                    false
                }
            });
        }
        if let ExprKind::Call { .. } = &expression.kind {
            return true;
        }
        self.expression_may_fail(id, facts, field)
    }

    pub(super) fn child_output_use(
        &self,
        child: parser::hir::TemplateId,
        applied: &AppliedComponentPort,
    ) -> Result<LocalOutputUse, SummaryBlocker> {
        let port = applied.port_summary().port();
        let indices = applied.port_summary().indices();
        self.with_local_template(child, applied.callee_evidence().context(), |_, _, facts| {
            let handle = facts
                .port_handle(port, indices)
                .map_err(|error| SummaryBlocker::LocalAnalysis(error.to_string()))?;
            self.local_handle_use_result(facts, &handle)
        })
    }

    /// Treat a declared output of the validated main template as environment-read.
    pub fn exported_main_output_use(
        &self,
        facts: &AnalysisFacts<'_>,
        main: &ContextEvidence,
        handle: &AccessHandle,
    ) -> SummaryFact<ProjectOutputUse> {
        SummaryFact::from_result(self.exported_output_result(facts, main, handle))
    }

    fn exported_output_result(
        &self,
        facts: &AnalysisFacts<'_>,
        main: &ContextEvidence,
        handle: &AccessHandle,
    ) -> Result<ProjectOutputUse, SummaryBlocker> {
        self.check_main_root(facts, main)?;
        if handle.component().is_some() {
            return Err(SummaryBlocker::WrongInstance);
        }
        let DefinitionRef::Template(id) = facts.definition() else {
            return Err(SummaryBlocker::WrongContext);
        };
        let indices = Self::local_indices(handle)?;
        let template = self.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
        let mut exported = false;
        for id in &template.ports {
            let port = self.hir().port(*id).ok_or(SummaryBlocker::ForeignDefinition)?;
            let checked_schema = match port.schema {
                PortSchema::Opaque(_) => false,
                PortSchema::Signal | PortSchema::Bus(_) => true,
            };
            if port.direction != Some(PortDirection::Output) || !checked_schema {
                continue;
            }
            if facts.port_handle(*id, &indices).ok().as_ref() == Some(handle) {
                exported = true;
                break;
            }
        }
        if !exported {
            return Err(SummaryBlocker::WrongInstance);
        }
        Ok(ProjectOutputUse {
            main: main.clone(),
            target: OutputTarget::Exported(Box::new(handle.clone())),
            status: ProjectOutputStatus::Read,
            source_reads: Vec::new(),
            source_span: handle.span(),
            instance_path: Vec::new(),
        })
    }

    fn local_indices(handle: &AccessHandle) -> Result<Vec<usize>, SummaryBlocker> {
        let mut indices = Vec::new();
        for step in &handle.path().steps {
            let AccessStep::Index { index: ArrayIndex::Constant(value), .. } = step else {
                return Err(SummaryBlocker::WrongInstance);
            };
            indices.push(value.parse().map_err(|_| SummaryBlocker::WrongInstance)?);
        }
        Ok(indices)
    }

    pub(super) fn check_main_root(
        &self,
        facts: &AnalysisFacts<'_>,
        main: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.check_main_identity(facts, main, MainSourceScope::WholeProject)
    }

    pub(super) fn check_model_main_root(
        &self,
        facts: &AnalysisFacts<'_>,
        main: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.check_main_identity(facts, main, MainSourceScope::ModelDefinitions)
    }

    fn check_main_identity(
        &self,
        facts: &AnalysisFacts<'_>,
        main: &ContextEvidence,
        source: MainSourceScope,
    ) -> Result<(), SummaryBlocker> {
        self.check_facts_for_evidence(facts, main)?;
        let complete = match source {
            MainSourceScope::WholeProject => self.source_complete(),
            MainSourceScope::ModelDefinitions => self.model_source_complete(facts.definition()),
        };
        if !complete || self.hir().mains().len() != 1 {
            return Err(SummaryBlocker::ExternalSummary);
        }
        let ContextOrigin::Main(id) = main.origin() else {
            return Err(SummaryBlocker::UnsupportedContext);
        };
        let site = self.graph().site(id).ok_or(SummaryBlocker::ForeignCall)?;
        if site.owner != CallOwner::Main(0) || site.resolved() != Some(facts.definition()) {
            return Err(SummaryBlocker::WrongContext);
        }
        if !*certified(&facts.reachable_node(facts.cfg().exit()))? {
            return Err(SummaryBlocker::ExternalSummary);
        }
        Ok(())
    }
}
