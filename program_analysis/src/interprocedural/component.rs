//! Checked binding of a local template port summary to one component instance.

use std::collections::BTreeMap;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use parser::hir::{
    AccessPath, AccessStep, DefinitionRef, Effect, ExprId, ExprKind, PortId, PortSchema, SymbolId,
};
use parser::new_frontend::PortDirection;

use crate::hir_cfg::{CfgNodeKind, DefinitionCfg, Origin};
use crate::hir_facts::{
    AccessHandle, AnalysisFacts, FieldValue, InstanceRelation, Range, VisitAccesses,
};

use super::summary::certified;
use super::{
    ContextEvidence, PortSummary, ProjectSummaries, ReachableCall, SummaryBlocker, SummaryFact,
};

/// A child-local output fact bound to one reachable, exact caller instance.
///
/// The binding does not prove that all caller-side input or output relations are closed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AppliedComponentPort {
    caller: ContextEvidence,
    callee: ContextEvidence,
    handle: AccessHandle,
    port: PortSummary,
    instantiation: NodeId,
}

/// An exact component output access observed in this caller's reachable CFG.
///
/// This certificate says only that the caller may read this output. It does
/// not prove the child is ready at the read or close all project-wide uses.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallerOutputRead {
    applied: AppliedComponentPort,
    read_origins: Vec<Origin>,
}

impl CallerOutputRead {
    #[must_use]
    pub fn applied_port(&self) -> &AppliedComponentPort {
        &self.applied
    }

    #[must_use]
    pub fn read_origins(&self) -> &[Origin] {
        &self.read_origins
    }
}

#[derive(Debug)]
pub(crate) enum LocalOutputUse {
    Read(Vec<Origin>),
    NoLocalRead,
}

#[derive(Clone, Copy)]
struct GeneratedPortEquality {
    input: PortId,
    origin: Origin,
}

struct ConstrainedInputBinding {
    port: PortId,
    value: FieldValue,
    origin: Origin,
    node: NodeId,
}

#[derive(Clone, Copy)]
enum ChildOutputEffect {
    Witness,
    Constraint,
    Opaque,
}

/// An output fixed by a child equality and an exact generated caller input binding.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ComposedConstraintFixedOutput {
    value: FieldValue,
    child_equality: Origin,
    caller_input: Origin,
    applied: AppliedComponentPort,
}

impl ComposedConstraintFixedOutput {
    #[must_use]
    pub fn value(&self) -> &FieldValue {
        &self.value
    }

    #[must_use]
    pub fn child_equality(&self) -> Origin {
        self.child_equality
    }

    #[must_use]
    pub fn caller_input(&self) -> Origin {
        self.caller_input
    }

    #[must_use]
    pub fn applied_port(&self) -> &AppliedComponentPort {
        &self.applied
    }
}

impl AppliedComponentPort {
    #[must_use]
    pub fn caller_evidence(&self) -> &ContextEvidence {
        &self.caller
    }

    #[must_use]
    pub fn callee_evidence(&self) -> &ContextEvidence {
        &self.callee
    }

    #[must_use]
    pub fn handle(&self) -> &AccessHandle {
        &self.handle
    }

    #[must_use]
    pub fn port_summary(&self) -> &PortSummary {
        &self.port
    }
}

impl ProjectSummaries<'_> {
    /// Certify an exact source read of this output in the bound caller context.
    ///
    /// Absence of a local read cannot certify a project-wide unused output.
    pub fn caller_output_read(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
    ) -> SummaryFact<CallerOutputRead> {
        let result = self.local_output_use_result(facts, applied).and_then(|use_state| {
            let LocalOutputUse::Read(read_origins) = use_state else {
                return Err(SummaryBlocker::ExternalSummary);
            };
            Ok(CallerOutputRead { applied: applied.clone(), read_origins })
        });
        SummaryFact::from_result(result)
    }

    pub(crate) fn local_output_use_result(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
    ) -> Result<LocalOutputUse, SummaryBlocker> {
        self.check_facts_for_evidence(facts, &applied.caller)?;
        if !applied.handle.matches_context(applied.caller.context()) {
            return Err(SummaryBlocker::WrongContext);
        }
        let reads = self.exact_output_reads(facts, applied);
        if !reads.is_empty() {
            return Ok(LocalOutputUse::Read(reads));
        }
        self.prove_no_local_output_read(facts, applied)?;
        Ok(LocalOutputUse::NoLocalRead)
    }

    fn exact_output_reads(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
    ) -> Vec<Origin> {
        let mut reads = Vec::new();
        for id in facts.cfg().nodes() {
            let Some(node) = facts.cfg().node(*id) else { continue };
            let CfgNodeKind::Evaluate(expression) = &node.kind else { continue };
            let Some(ExprKind::Access(path)) =
                self.hir().expression(*expression).map(|expr| &expr.kind)
            else {
                continue;
            };
            if facts.handle_relation(&applied.handle, path) != InstanceRelation::Exact {
                continue;
            }
            if facts.reachable_node(*id).certified() == Some(&true) {
                if let Some(origin) = node.origin {
                    reads.push(origin);
                }
            }
        }
        reads
    }

    fn prove_no_local_output_read(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
    ) -> Result<(), SummaryBlocker> {
        if !*certified(&facts.reachable_node(facts.cfg().exit()))? {
            return Err(SummaryBlocker::ExternalSummary);
        }
        let mut uncertain = false;
        for id in facts.cfg().nodes() {
            let Some(node) = facts.cfg().node(*id) else {
                return Err(SummaryBlocker::ExternalSummary);
            };
            if !*certified(&facts.reachable_node(*id))? {
                continue;
            }
            match &node.kind {
                CfgNodeKind::Evaluate(expression) => {
                    let expr = self
                        .hir()
                        .expression(*expression)
                        .ok_or(SummaryBlocker::ExternalSummary)?;
                    match &expr.kind {
                        ExprKind::Access(path) => {
                            match facts.handle_relation(&applied.handle, path) {
                                InstanceRelation::Exact => uncertain = true,
                                InstanceRelation::Possible => uncertain = true,
                                InstanceRelation::Separate => {}
                            }
                        }
                        ExprKind::Opaque(_) | ExprKind::AnonymousComponent { .. } => {
                            uncertain = true;
                        }
                        _ => {}
                    }
                }
                CfgNodeKind::Opaque(_)
                | CfgNodeKind::OpaqueAssignment { .. }
                | CfgNodeKind::OpaqueEquality { .. }
                | CfgNodeKind::DeferredAssignment { .. }
                | CfgNodeKind::Log => uncertain = true,
                _ => {}
            }
        }
        if uncertain {
            return Err(SummaryBlocker::ExternalSummary);
        }
        self.linear_caller_path(facts)?;
        Ok(())
    }

    /// Prove an output value through a must-generated child equality and caller input.
    pub fn composed_constraint_fixed_output(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
    ) -> SummaryFact<ComposedConstraintFixedOutput> {
        SummaryFact::from_result(self.composed_value_result(facts, applied))
    }

    fn composed_value_result(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
    ) -> Result<ComposedConstraintFixedOutput, SummaryBlocker> {
        self.check_facts_for_evidence(facts, &applied.caller)?;
        if !applied.handle.matches_context(applied.caller.context()) {
            return Err(SummaryBlocker::WrongContext);
        }
        let order = self.linear_caller_path(facts)?;
        if !*certified(&facts.must_execute(applied.instantiation))? {
            return Err(SummaryBlocker::ExternalSummary);
        }
        let DefinitionRef::Template(child) = applied.callee.context().definition() else {
            return Err(SummaryBlocker::WrongInstance);
        };
        let equality = self.child_output_equality(child, applied)?;
        let bindings = self.all_input_bindings(facts, applied, child, &order)?;
        for binding in &bindings {
            self.check_output_read_order(facts, applied, binding.node, &order)?;
        }
        let binding = bindings
            .into_iter()
            .find(|item| item.port == equality.input)
            .ok_or(SummaryBlocker::MissingInputBinding)?;
        Ok(ComposedConstraintFixedOutput {
            value: binding.value,
            child_equality: equality.origin,
            caller_input: binding.origin,
            applied: applied.clone(),
        })
    }

    fn linear_caller_path(
        &self,
        facts: &AnalysisFacts<'_>,
    ) -> Result<BTreeMap<NodeId, usize>, SummaryBlocker> {
        let cfg = facts.cfg();
        let mut positions = BTreeMap::new();
        let mut current = cfg.entry();
        while current != cfg.exit() {
            let position = positions.len();
            if positions.insert(current, position).is_some() {
                return Err(SummaryBlocker::UnsupportedContext);
            }
            let mut next = None;
            for id in cfg.edges() {
                let edge = cfg.edge(*id).ok_or(SummaryBlocker::ExternalSummary)?;
                if edge.source == current && next.replace(edge.target).is_some() {
                    return Err(SummaryBlocker::UnsupportedContext);
                }
            }
            current = next.ok_or(SummaryBlocker::ExternalSummary)?;
        }
        Ok(positions)
    }

    /// Bind one child output summary to a proved caller call and exact instance.
    pub fn apply_component_output(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
        call: &ReachableCall<'_>,
        handle: &AccessHandle,
    ) -> SummaryFact<AppliedComponentPort> {
        SummaryFact::from_result(self.component_output_result(facts, caller, call, handle))
    }

    fn component_output_result(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
        call: &ReachableCall<'_>,
        handle: &AccessHandle,
    ) -> Result<AppliedComponentPort, SummaryBlocker> {
        self.check_facts_for_evidence(facts, caller)?;
        let DefinitionRef::Template(template) = call.callee() else {
            return Err(SummaryBlocker::WrongInstance);
        };
        if !handle.matches_context(caller.context()) {
            return Err(SummaryBlocker::WrongContext);
        }
        let component = handle.component().ok_or(SummaryBlocker::WrongInstance)?;
        let component = facts.hir().component(component).ok_or(SummaryBlocker::WrongInstance)?;
        if handle.path().root != component.symbol {
            return Err(SummaryBlocker::WrongInstance);
        }
        let instantiation = self.bind_instantiation(facts, call, handle)?;
        let callee = self.call_evidence(call, facts, caller)?;
        let (port, indices) = handle.output_port().ok_or(SummaryBlocker::WrongInstance)?;
        let summary = self.template_port_at(template, callee.context(), port, &indices);
        let port = summary.certified().cloned().ok_or_else(|| {
            summary
                .unavailable()
                .and_then(|blockers| blockers.iter().next())
                .cloned()
                .unwrap_or(SummaryBlocker::ExternalSummary)
        })?;
        Ok(AppliedComponentPort {
            caller: caller.clone(),
            callee,
            handle: handle.clone(),
            port,
            instantiation,
        })
    }

    fn bind_instantiation(
        &self,
        facts: &AnalysisFacts<'_>,
        call: &ReachableCall<'_>,
        handle: &AccessHandle,
    ) -> Result<NodeId, SummaryBlocker> {
        let cfg = facts.cfg();
        let mut count = 0;
        let mut matched = None;
        for id in cfg.nodes() {
            let Some(CfgNodeKind::Instantiate { target, value }) =
                cfg.node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            if target.root != handle.path().root {
                continue;
            }
            let relation = facts.instance_relation(handle, target);
            if relation == InstanceRelation::Separate {
                continue;
            }
            match facts.reachable_node(*id).certified() {
                Some(false) => continue,
                None => return Err(SummaryBlocker::ExternalSummary),
                Some(true) => {}
            }
            if relation == InstanceRelation::Possible {
                return Err(SummaryBlocker::SymbolicInstance);
            }
            count += 1;
            if self.direct_call_expression(*value) == call.site().expression {
                matched = Some(*id);
            }
        }
        if count > 1 {
            return Err(SummaryBlocker::DuplicateInstance);
        }
        matched.ok_or(SummaryBlocker::WrongInstance)
    }

    fn child_output_equality(
        &self,
        child: parser::hir::TemplateId,
        applied: &AppliedComponentPort,
    ) -> Result<GeneratedPortEquality, SummaryBlocker> {
        self.check_evidence(&applied.callee)?;
        if !applied.port.indices().is_empty() {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        self.with_local_template(child, applied.callee.context(), |template, cfg, facts| {
            self.reject_reachable_child_loop(cfg, facts)?;
            let output =
                self.hir().port(applied.port.port()).ok_or(SummaryBlocker::ForeignDefinition)?;
            let symbol =
                self.hir().symbol(output.symbol).ok_or(SummaryBlocker::ForeignDefinition)?;
            if symbol.rank != 0 || output.schema != PortSchema::Signal {
                return Err(SummaryBlocker::UnsupportedContext);
            }
            let mut result = None;
            for id in cfg.nodes() {
                let Some(node) = cfg.node(*id) else { continue };
                let CfgNodeKind::Constraint { target: Some(target), left, right: None } =
                    &node.kind
                else {
                    continue;
                };
                if target.root != output.symbol || !target.steps.is_empty() {
                    continue;
                }
                let Some(ExprKind::Access(source)) =
                    self.hir().expression(*left).map(|expr| &expr.kind)
                else {
                    continue;
                };
                let Some(input) = self.exact_input_port(template, source) else {
                    continue;
                };
                if !*certified(&facts.must_execute(*id))? || result.is_some() {
                    return Err(SummaryBlocker::ExternalSummary);
                }
                let origin = node
                    .origin
                    .ok_or(SummaryBlocker::LocalAnalysis("missing child equality origin".into()))?;
                result = Some(GeneratedPortEquality { input, origin });
            }
            let equality = result.ok_or(SummaryBlocker::ExternalSummary)?;
            self.check_child_output_effects(cfg, facts, output.symbol, equality.origin)?;
            Ok(equality)
        })
    }

    fn reject_reachable_child_loop(
        &self,
        cfg: &DefinitionCfg,
        facts: &AnalysisFacts<'_>,
    ) -> Result<(), SummaryBlocker> {
        for id in cfg.nodes() {
            if let Some(CfgNodeKind::LoopHeader) = cfg.node(*id).map(|node| &node.kind) {
                if *certified(&facts.reachable_node(*id))? {
                    return Err(SummaryBlocker::UnsupportedContext);
                }
            }
        }
        Ok(())
    }

    fn check_child_output_effects(
        &self,
        cfg: &DefinitionCfg,
        facts: &AnalysisFacts<'_>,
        output: SymbolId,
        selected: Origin,
    ) -> Result<(), SummaryBlocker> {
        let mut witnesses = 0;
        let mut constraints = 0;
        for id in cfg.nodes() {
            let Some(node) = cfg.node(*id) else { continue };
            if !*certified(&facts.reachable_node(*id))? {
                continue;
            }
            match self.child_output_effect(&node.kind, output)? {
                Some(ChildOutputEffect::Witness) if node.origin == Some(selected) => {
                    witnesses += 1;
                }
                Some(ChildOutputEffect::Constraint) if node.origin == Some(selected) => {
                    constraints += 1;
                }
                Some(ChildOutputEffect::Witness | ChildOutputEffect::Constraint)
                | Some(ChildOutputEffect::Opaque) => {
                    return Err(SummaryBlocker::ExternalSummary);
                }
                None => {}
            }
        }
        if witnesses == 1 && constraints == 1 {
            Ok(())
        } else {
            Err(SummaryBlocker::ExternalSummary)
        }
    }

    fn child_output_effect(
        &self,
        node: &CfgNodeKind,
        output: SymbolId,
    ) -> Result<Option<ChildOutputEffect>, SummaryBlocker> {
        if let CfgNodeKind::Witness { target, .. } = node {
            return Ok((target.root == output).then_some(ChildOutputEffect::Witness));
        }
        if let CfgNodeKind::Constraint { target, left, right } = node {
            let touches = self.constraint_touches_output(target.as_ref(), *left, *right, output)?;
            return Ok(touches.then_some(ChildOutputEffect::Constraint));
        }
        if let CfgNodeKind::OpaqueAssignment { target, .. } = node {
            return Ok((target.root == output).then_some(ChildOutputEffect::Opaque));
        }
        if let CfgNodeKind::OpaqueEquality { left, right, .. } = node {
            let touches = self.expression_touches_output(*left, output)?
                || self.expression_touches_output(*right, output)?;
            return Ok(touches.then_some(ChildOutputEffect::Opaque));
        }
        Ok(None)
    }

    fn constraint_touches_output(
        &self,
        target: Option<&AccessPath>,
        left: ExprId,
        right: Option<ExprId>,
        output: SymbolId,
    ) -> Result<bool, SummaryBlocker> {
        let Some(target) = target else {
            let left_touches = self.expression_touches_output(left, output)?;
            let right_touches = match right {
                Some(value) => self.expression_touches_output(value, output)?,
                None => false,
            };
            return Ok(left_touches || right_touches);
        };
        Ok(target.root == output)
    }

    fn expression_touches_output(
        &self,
        expression: ExprId,
        output: SymbolId,
    ) -> Result<bool, SummaryBlocker> {
        let mut touches = false;
        if expression.visit_accesses(self.hir(), &mut |path| touches |= path.root == output) {
            Ok(touches)
        } else {
            Err(SummaryBlocker::ExternalSummary)
        }
    }

    fn exact_input_port(
        &self,
        template: &parser::hir::Template,
        source: &AccessPath,
    ) -> Option<PortId> {
        if !source.steps.is_empty() {
            return None;
        }
        template.ports.iter().copied().find(|id| {
            self.hir().port(*id).is_some_and(|port| {
                port.symbol == source.root && port.direction == Some(PortDirection::Input)
            })
        })
    }

    fn all_input_bindings(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
        child: parser::hir::TemplateId,
        order: &BTreeMap<NodeId, usize>,
    ) -> Result<Vec<ConstrainedInputBinding>, SummaryBlocker> {
        let template = self.hir().template(child).ok_or(SummaryBlocker::ForeignDefinition)?;
        let mut bindings = Vec::new();
        for id in &template.ports {
            let port = self.hir().port(*id).ok_or(SummaryBlocker::ForeignDefinition)?;
            if port.direction != Some(PortDirection::Input) {
                continue;
            }
            let symbol = self.hir().symbol(port.symbol).ok_or(SummaryBlocker::ForeignDefinition)?;
            if symbol.rank != 0 {
                return Err(SummaryBlocker::UnsupportedContext);
            }
            bindings.push(self.caller_input_binding(facts, applied, *id, order)?);
        }
        Ok(bindings)
    }

    fn caller_input_binding(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
        input: PortId,
        order: &BTreeMap<NodeId, usize>,
    ) -> Result<ConstrainedInputBinding, SummaryBlocker> {
        let cfg = facts.cfg();
        let mut binding = None;
        for id in cfg.nodes() {
            let Some(node) = cfg.node(*id) else { continue };
            let CfgNodeKind::Witness { target, value } = &node.kind else { continue };
            if target.root != applied.handle.path().root || !self.targets_port(target, input) {
                continue;
            }
            let relation = facts.instance_relation(&applied.handle, target);
            if relation == InstanceRelation::Separate {
                continue;
            }
            if !*certified(&facts.reachable_node(*id))? {
                continue;
            }
            if relation == InstanceRelation::Possible {
                return Err(SummaryBlocker::SymbolicInstance);
            }
            if binding.is_some() {
                return Err(SummaryBlocker::DuplicateInputBinding);
            }
            let origin = node
                .origin
                .ok_or(SummaryBlocker::LocalAnalysis("missing caller input origin".into()))?;
            self.checked_input_effect(origin)?;
            let current = order.get(id).ok_or(SummaryBlocker::ExternalSummary)?;
            let instantiated =
                order.get(&applied.instantiation).ok_or(SummaryBlocker::ExternalSummary)?;
            if current <= instantiated || !*certified(&facts.must_execute(*id))? {
                return Err(SummaryBlocker::ExternalSummary);
            }
            let value = match certified(&facts.range(*value))? {
                Range::Exact(value) => value.clone(),
                Range::Canonical | Range::Unreachable => {
                    return Err(SummaryBlocker::UnsupportedContext);
                }
            };
            binding = Some(ConstrainedInputBinding { port: input, value, origin, node: *id });
        }
        binding.ok_or(SummaryBlocker::MissingInputBinding)
    }

    fn targets_port(&self, target: &AccessPath, port: PortId) -> bool {
        let steps = &target.steps;
        let Some(position) = steps.iter().position(|step| match step {
            AccessStep::Port { .. } => true,
            AccessStep::Index { .. } | AccessStep::Tag { .. } => false,
        }) else {
            return false;
        };
        match steps.get(position) {
            Some(AccessStep::Port { port: actual, .. }) => {
                *actual == port && position + 1 == steps.len()
            }
            Some(AccessStep::Index { .. } | AccessStep::Tag { .. }) | None => false,
        }
    }

    fn checked_input_effect(&self, origin: Origin) -> Result<(), SummaryBlocker> {
        let effect = self
            .hir()
            .block(origin.block)
            .and_then(|block| block.effects.get(origin.effect_index))
            .ok_or(SummaryBlocker::ExternalSummary)?;
        match effect {
            Effect::ConstraintAssignment { .. } => Ok(()),
            Effect::WitnessAssignment { .. } => Err(SummaryBlocker::WitnessOnlyInput),
            _ => Err(SummaryBlocker::ExternalSummary),
        }
    }

    fn check_output_read_order(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
        input: NodeId,
        order: &BTreeMap<NodeId, usize>,
    ) -> Result<(), SummaryBlocker> {
        let bound_at = order.get(&input).ok_or(SummaryBlocker::ExternalSummary)?;
        for id in facts.cfg().nodes() {
            let Some(CfgNodeKind::Evaluate(expr)) = facts.cfg().node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            let Some(ExprKind::Access(path)) = self.hir().expression(*expr).map(|item| &item.kind)
            else {
                continue;
            };
            if path.root != applied.handle.path().root
                || path.terminal != applied.handle.path().terminal
                || facts.instance_relation(&applied.handle, path) == InstanceRelation::Separate
            {
                continue;
            }
            if order.get(id).is_some_and(|position| position <= bound_at)
                && *certified(&facts.reachable_node(*id))?
            {
                return Err(SummaryBlocker::ExternalSummary);
            }
        }
        Ok(())
    }

    fn direct_call_expression(&self, expression: ExprId) -> Option<ExprId> {
        let expression_node = self.hir().expression(expression)?;
        match expression_node.kind {
            ExprKind::Parallel(inner) => self.direct_call_expression(inner),
            ExprKind::Call { .. } => Some(expression),
            ExprKind::Number(_)
            | ExprKind::Access(_)
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Array(_)
            | ExprKind::Tuple(_)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Ternary { .. }
            | ExprKind::Opaque(_) => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use parser::hir::{lift_project, DefinitionRef};
    use parser::new_frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::build_cfg;
    use crate::interprocedural::{CallOwner, CallReachability, ProjectSummaries, SummaryBlocker};

    use super::LocalOutputUse;

    fn local_output_state(source: &str, instance: usize) -> Result<LocalOutputUse, SummaryBlocker> {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-local-output-use-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let file = directory.join("case.circom");
        std::fs::write(&file, source).unwrap();
        let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let parent = lifted.hir.definition("Parent").unwrap();
        let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
            panic!("Child must be a template")
        };
        let cfg = build_cfg(&lifted.hir, parent).unwrap();
        let scope = provider.symbolic_root(parent).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &scope, None).unwrap();
        let output = lifted.hir.template(child).unwrap().ports[0];
        let component = lifted.hir.components()[0].id;
        let handle = facts.component_output_handle(component, &[instance], output, &[]).unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(parent))[instance];
        let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
        else {
            panic!("second instance must be reachable")
        };
        let applied = provider.apply_component_output(&facts, &scope, &call, &handle);
        let Some(applied) = applied.certified() else {
            return Err(applied
                .unavailable()
                .and_then(|blockers| blockers.iter().next())
                .cloned()
                .unwrap_or(SummaryBlocker::ExternalSummary));
        };
        provider.local_output_use_result(&facts, applied)
    }

    #[test]
    fn an_untouched_sibling_has_only_a_local_no_read_certificate() {
        let result = local_output_state(
            concat!(
                "template Child(){signal output out;out<==1;} ",
                "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
                "signal output y;y<==c[0].out;}"
            ),
            1,
        );
        assert!(matches!(result, Ok(LocalOutputUse::NoLocalRead)));
    }

    #[test]
    fn a_bus_field_read_blocks_no_local_read_for_the_whole_output() {
        let result = local_output_state(
            concat!(
                "bus B(){signal leaf;} template Child(){B output out;} ",
                "template Parent(){component c[2];c[0]=Child();c[1]=Child();",
                "signal output y;y<==c[0].out.leaf;}"
            ),
            0,
        );
        assert!(!matches!(result, Ok(LocalOutputUse::NoLocalRead)), "{result:?}");
    }
}
