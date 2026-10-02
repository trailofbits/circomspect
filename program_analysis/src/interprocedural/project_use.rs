//! Output-use proofs scoped to a validated, closed `main` root.

use std::collections::BTreeSet;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use parser::hir::{
    AccessStep, ArrayIndex, BusTarget, CallTarget, ControlGuard, DefinitionRef, ExprId, ExprKind,
    PortSchema, Symbol, SymbolId, SymbolKind,
};
use parser::new_frontend::{AssignmentOperator, PortDirection};

use crate::hir_cfg::{build_cfg, CfgNodeKind, DefinitionCfg, Origin};
use crate::hir_facts::{AccessHandle, AnalysisFacts, FieldContext, Range};
use crate::interprocedural::input_relation::ready_instance_at_use;

use super::component::LocalOutputUse;
use super::summary::{certified, is_proven_nonzero};
use super::{
    AppliedComponentPort, CallOwner, CallReachability, ContextEvidence, ContextOrigin,
    ProjectSummaries, SummaryBlocker, SummaryFact,
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

/// A project-wide output-use result for the bounded direct-main subset.
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
}

impl ProjectSummaries<'_> {
    /// Prove use or non-use of an exact direct child of validated main.
    ///
    /// An input-bearing child requires a scalar component and certified scalar
    /// bindings. It is the only reachable component instance in this bounded
    /// project closure.
    pub fn closed_main_component_output_use(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
    ) -> SummaryFact<ProjectOutputUse> {
        SummaryFact::from_result(self.closed_component_result(facts, applied))
    }

    fn closed_component_result(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
    ) -> Result<ProjectOutputUse, SummaryBlocker> {
        let main = applied.caller_evidence();
        self.check_main_root(facts, main)?;
        let DefinitionRef::Template(child) = applied.callee_evidence().context().definition()
        else {
            return Err(SummaryBlocker::WrongInstance);
        };
        let template = self.hir().template(child).ok_or(SummaryBlocker::ForeignDefinition)?;
        let mut has_inputs = false;
        for id in &template.ports {
            let port = self.hir().port(*id).ok_or(SummaryBlocker::ForeignDefinition)?;
            if port.direction == Some(PortDirection::Input) {
                has_inputs = true;
            }
        }
        self.check_parent_components_complete(facts)?;
        self.check_template_execution(facts.cfg(), facts)?;
        self.check_direct_siblings(facts, applied, has_inputs)?;
        if has_inputs {
            let root = applied.handle().path().root;
            let component = self.hir().symbol(root).ok_or(SummaryBlocker::ForeignDefinition)?;
            if component.rank != 0 {
                return Err(SummaryBlocker::UnsupportedContext);
            }
            ready_instance_at_use(facts, applied, child)?;
        }
        self.check_child_has_no_components(child, applied)?;
        self.with_local_template(child, applied.callee_evidence().context(), |_, cfg, facts| {
            self.check_template_execution(cfg, facts)
        })?;
        let use_state = self.local_output_use_result(facts, applied)?;
        let use_state = match use_state {
            LocalOutputUse::Read(sites) => LocalOutputUse::Read(sites),
            LocalOutputUse::NoLocalRead => self.child_output_use(child, applied)?,
        };
        let (status, source_reads) = match use_state {
            LocalOutputUse::Read(sites) => (ProjectOutputStatus::Read, sites),
            LocalOutputUse::NoLocalRead => (ProjectOutputStatus::Unused, Vec::new()),
        };
        Ok(ProjectOutputUse {
            main: main.clone(),
            target: OutputTarget::Component(Box::new(applied.clone())),
            status,
            source_reads,
        })
    }

    fn check_parent_components_complete(
        &self,
        facts: &AnalysisFacts<'_>,
    ) -> Result<(), SummaryBlocker> {
        for component in self.hir().components() {
            if !facts.cfg().owns_symbol(component.symbol) {
                continue;
            }
            self.check_component_complete(facts, component)?;
        }
        Ok(())
    }

    fn check_component_complete(
        &self,
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

    fn check_direct_siblings(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
        has_inputs: bool,
    ) -> Result<(), SummaryBlocker> {
        for id in facts.cfg().nodes() {
            if *id == applied.instantiation() {
                continue;
            }
            let Some(CfgNodeKind::Instantiate { value, .. }) =
                facts.cfg().node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            if !*certified(&facts.reachable_node(*id))? {
                continue;
            }
            if has_inputs {
                return Err(SummaryBlocker::UnsupportedContext);
            }
            self.check_no_input_sibling(facts, *value, applied.caller_evidence())?;
        }
        Ok(())
    }

    fn check_no_input_sibling(
        &self,
        facts: &AnalysisFacts<'_>,
        value: ExprId,
        caller: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        let expression = self.hir().expression(value).ok_or(SummaryBlocker::ExternalSummary)?;
        let Some(CallTarget::Template(template)) = expression.call_target() else {
            return Err(SummaryBlocker::ExternalSummary);
        };
        let template = self.hir().template(*template).ok_or(SummaryBlocker::ForeignDefinition)?;
        for port in &template.ports {
            let port = self.hir().port(*port).ok_or(SummaryBlocker::ForeignDefinition)?;
            if port.direction == Some(PortDirection::Input) {
                return Err(SummaryBlocker::UnsupportedContext);
            }
        }
        for site in
            self.graph().calls_from(CallOwner::Definition(DefinitionRef::Template(template.id)))
        {
            if let Some(DefinitionRef::Function(_)) = site.resolved() {
                continue;
            }
            return Err(SummaryBlocker::UnsupportedContext);
        }
        let owner = CallOwner::Definition(facts.definition());
        let site = self
            .graph()
            .calls_from(owner)
            .into_iter()
            .find(|site| site.expression == Some(value))
            .ok_or(SummaryBlocker::ExternalSummary)?;
        let CallReachability::Reachable(call) = self.graph().reachable_call(site.id(), facts)
        else {
            return Err(SummaryBlocker::ExternalSummary);
        };
        let evidence = self.call_evidence(&call, facts, caller)?;
        self.with_local_template(template.id, evidence.context(), |_, cfg, facts| {
            self.check_template_execution(cfg, facts)
        })?;
        Ok(())
    }

    fn check_child_has_no_components(
        &self,
        child: parser::hir::TemplateId,
        applied: &AppliedComponentPort,
    ) -> Result<(), SummaryBlocker> {
        self.with_local_template(child, applied.callee_evidence().context(), |_, cfg, facts| {
            for id in cfg.nodes() {
                let node = cfg.node(*id).ok_or(SummaryBlocker::ExternalSummary)?;
                let mut nested = false;
                if let CfgNodeKind::Instantiate { .. } = &node.kind {
                    nested = true;
                }
                if let CfgNodeKind::Evaluate(id) = &node.kind {
                    let expr = self.hir().expression(*id).ok_or(SummaryBlocker::ExternalSummary)?;
                    if let ExprKind::AnonymousComponent { .. } = &expr.kind {
                        nested = true;
                    }
                }
                if nested && *certified(&facts.reachable_node(*id))? {
                    return Err(SummaryBlocker::UnsupportedContext);
                }
            }
            Ok(())
        })
    }

    fn check_template_execution(
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

    fn child_output_use(
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

    fn check_main_root(
        &self,
        facts: &AnalysisFacts<'_>,
        main: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.check_facts_for_evidence(facts, main)?;
        if !self.source_complete() || self.hir().mains().len() != 1 {
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
