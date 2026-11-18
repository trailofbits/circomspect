//! Checked binding of a local template port summary to one component instance.

pub(in crate::interprocedural) mod binding;

use std::collections::BTreeSet;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use parser::hir::{AccessPath, DefinitionRef, ExprId, ExprKind, PortId, PortSchema, SymbolId};
use parser::frontend::PortDirection;

use crate::hir_cfg::{Constraint, CfgNodeKind, DefinitionCfg, Origin};
use crate::hir_facts::{AccessHandle, AnalysisFacts, FieldValue, InstanceRelation, VisitAccesses};

use crate::interprocedural::input_relation::ready_instance_at_use;
use super::summary::certified;
use super::{ContextEvidence, PortSummary, ProjectAnalysis, ReachableCall, SummaryBlocker, SummaryFact};

/// A child-local output fact bound to one reachable, exact caller instance.
///
/// The binding does not prove that all caller-side input or output relations are closed.
///
/// Issued through checked component binding for one selected instance and port. It retains
/// caller/callee evidence, call site, checked handle, and indices. It does not by itself prove
/// input initialization, generated equations, or complete child generation.
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
    caller_inputs: Vec<Origin>,
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
    pub fn caller_inputs(&self) -> &[Origin] {
        &self.caller_inputs
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

    pub(super) fn instantiation(&self) -> NodeId {
        self.instantiation
    }
}

/// Component instance binding, output use, and composition queries for one session.
pub struct ComponentQueries<'session, 'hir> {
    pub(super) analysis: &'session ProjectAnalysis<'hir>,
}

impl ComponentQueries<'_, '_> {
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
        self.analysis.contexts().check_facts_for_evidence(facts, &applied.caller)?;
        if !applied.handle.matches_context(applied.caller.context()) {
            return Err(SummaryBlocker::WrongContext);
        }
        self.local_handle_use_result(facts, &applied.handle)
    }

    pub(super) fn local_handle_use_result(
        &self,
        facts: &AnalysisFacts<'_>,
        handle: &AccessHandle,
    ) -> Result<LocalOutputUse, SummaryBlocker> {
        let reads = self.exact_output_reads(facts, handle);
        if !reads.is_empty() {
            return Ok(LocalOutputUse::Read(reads));
        }
        self.prove_no_local_output_read(facts, handle)?;
        Ok(LocalOutputUse::NoLocalRead)
    }

    fn exact_output_reads(&self, facts: &AnalysisFacts<'_>, handle: &AccessHandle) -> Vec<Origin> {
        let mut reads = Vec::new();
        for id in facts.cfg().nodes() {
            let Some(node) = facts.cfg().node(*id) else { continue };
            let CfgNodeKind::Evaluate(expression) = &node.kind else { continue };
            let Some(ExprKind::Access(path)) =
                self.analysis.hir().expression(*expression).map(|expr| &expr.kind)
            else {
                continue;
            };
            if facts.handle_relation(handle, path) != InstanceRelation::Exact {
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
        handle: &AccessHandle,
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
                        .analysis
                        .hir()
                        .expression(*expression)
                        .ok_or(SummaryBlocker::ExternalSummary)?;
                    match &expr.kind {
                        ExprKind::Access(path) => match facts.handle_relation(handle, path) {
                            InstanceRelation::Exact | InstanceRelation::Possible => {
                                uncertain = true;
                            }
                            InstanceRelation::Separate => {}
                        },
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
        Self::require_linear_caller_path(facts.cfg(), facts.cfg().entry(), facts.cfg().exit())?;
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
        self.analysis.contexts().check_facts_for_evidence(facts, &applied.caller)?;
        if !applied.handle.matches_context(applied.caller.context()) {
            return Err(SummaryBlocker::WrongContext);
        }
        if !*certified(&facts.must_execute(applied.instantiation))? {
            return Err(SummaryBlocker::ExternalSummary);
        }
        let DefinitionRef::Template(child) = applied.callee.context().definition() else {
            return Err(SummaryBlocker::WrongInstance);
        };
        let equality = self.child_output_equality(child, applied)?;
        let ready = ready_instance_at_use(facts, applied, child)?;
        let binding = ready.binding(equality.input).ok_or(SummaryBlocker::MissingInputBinding)?;
        let crate::interprocedural::input_relation::GeneratedInputValue::Constant(value) =
            &binding.value
        else {
            return Err(SummaryBlocker::UnsupportedContext);
        };
        Ok(ComposedConstraintFixedOutput {
            value: value.clone(),
            child_equality: equality.origin,
            caller_inputs: binding.origins.clone(),
            applied: applied.clone(),
        })
    }

    fn require_linear_caller_path<G: FlowGraph<NodeId = NodeId>>(
        cfg: &G,
        entry: NodeId,
        exit: NodeId,
    ) -> Result<(), SummaryBlocker> {
        let mut visited = BTreeSet::new();
        let mut current = entry;
        while current != exit {
            if !visited.insert(current) {
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
        Ok(())
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

    fn child_output_equality(
        &self,
        child: parser::hir::TemplateId,
        applied: &AppliedComponentPort,
    ) -> Result<GeneratedPortEquality, SummaryBlocker> {
        self.analysis.contexts().check_evidence(&applied.callee)?;
        if !applied.port.indices().is_empty() {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        self.analysis.templates().with_local_template(
            child,
            applied.callee.context(),
            |template, cfg, facts| {
                Self::reject_reachable_child_loop(cfg, facts)?;
                let output = self
                    .analysis
                    .hir()
                    .port(applied.port.port())
                    .ok_or(SummaryBlocker::ForeignDefinition)?;
                let symbol = self
                    .analysis
                    .hir()
                    .symbol(output.symbol)
                    .ok_or(SummaryBlocker::ForeignDefinition)?;
                if symbol.rank != 0 || output.schema != PortSchema::Signal {
                    return Err(SummaryBlocker::UnsupportedContext);
                }
                let mut result = None;
                for id in cfg.nodes() {
                    let Some(node) = cfg.node(*id) else { continue };
                    let CfgNodeKind::Constraint(Constraint::Assignment { target, value }) =
                        &node.kind
                    else {
                        continue;
                    };
                    if target.root != output.symbol || !target.steps.is_empty() {
                        continue;
                    }
                    let Some(ExprKind::Access(source)) =
                        self.analysis.hir().expression(*value).map(|expr| &expr.kind)
                    else {
                        continue;
                    };
                    let Some(input) = self.exact_input_port(template, source) else {
                        continue;
                    };
                    if !*certified(&facts.must_execute(*id))? || result.is_some() {
                        return Err(SummaryBlocker::ExternalSummary);
                    }
                    let origin = node.origin.ok_or(SummaryBlocker::LocalAnalysis(
                        "missing child equality origin".into(),
                    ))?;
                    result = Some(GeneratedPortEquality { input, origin });
                }
                let equality = result.ok_or(SummaryBlocker::ExternalSummary)?;
                self.check_child_output_effects(cfg, facts, output.symbol, equality.origin)?;
                Ok(equality)
            },
        )
    }

    fn reject_reachable_child_loop(
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
                Some(
                    ChildOutputEffect::Witness
                    | ChildOutputEffect::Constraint
                    | ChildOutputEffect::Opaque,
                ) => {
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
        if let CfgNodeKind::Constraint(constraint) = node {
            let touches = self.constraint_touches_output(constraint, output)?;
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
        constraint: &Constraint,
        output: SymbolId,
    ) -> Result<bool, SummaryBlocker> {
        match constraint {
            Constraint::Assignment { target, .. } => Ok(target.root == output),
            Constraint::Equality { left, right } => {
                let left_touches = self.expression_touches_output(*left, output)?;
                let right_touches = self.expression_touches_output(*right, output)?;
                Ok(left_touches || right_touches)
            }
        }
    }

    fn expression_touches_output(
        &self,
        expression: ExprId,
        output: SymbolId,
    ) -> Result<bool, SummaryBlocker> {
        let mut touches = false;
        if expression
            .visit_accesses(self.analysis.hir(), &mut |path| touches |= path.root == output)
        {
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
            self.analysis.hir().port(*id).is_some_and(|port| {
                port.symbol == source.root && port.direction == Some(PortDirection::Input)
            })
        })
    }

    fn direct_call_expression(&self, expression: ExprId) -> Option<ExprId> {
        let expression_node = self.analysis.hir().expression(expression)?;
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
    use parser::frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::build_cfg;
    use crate::interprocedural::{
        CallOwner, CallReachability, ComponentQueries, ProjectAnalysis, SummaryBlocker,
    };

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
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let parent = lifted.hir.definition("Parent").unwrap();
        let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
            panic!("Child must be a template")
        };
        let cfg = build_cfg(&lifted.hir, parent).unwrap();
        let scope = provider.contexts().symbolic_root(parent).unwrap();
        let facts = provider.contexts().analyze_for_evidence(&cfg, &scope, None).unwrap();
        let output = lifted.hir.template(child).unwrap().ports[0];
        let component = lifted.hir.components()[0].id;
        let handle = facts.component_output_handle(component, &[instance], output, &[]).unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(parent))[instance];
        let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
        else {
            panic!("second instance must be reachable")
        };
        let applied = provider.components().apply_component_output(&facts, &scope, &call, &handle);
        let Some(applied) = applied.certified() else {
            return Err(applied
                .unavailable()
                .and_then(|blockers| blockers.iter().next())
                .cloned()
                .unwrap_or(SummaryBlocker::ExternalSummary));
        };
        provider.components().local_output_use_result(&facts, applied)
    }

    #[test]
    fn local_no_read_path_requires_linear_source_control() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-linear-caller-{}-{:?}",
            std::process::id(),
            std::thread::current().id(),
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let file = directory.join("case.circom");
        for (source, expected) in [
            ("template Parent(){var x=1;}", Ok(())),
            ("template Parent(n){if(n){var y=1;}}", Err(SummaryBlocker::UnsupportedContext)),
            ("template Parent(n){while(n){var y=1;}}", Err(SummaryBlocker::UnsupportedContext)),
        ] {
            std::fs::write(&file, source).unwrap();
            let loaded = load_sources(
                std::slice::from_ref(&file),
                std::slice::from_ref(&directory),
                VersionPolicy::new(Version::new(2, 2, 3)),
            );
            let lifted = lift_project(&loaded);
            let cfg = build_cfg(&lifted.hir, lifted.hir.definition("Parent").unwrap()).unwrap();
            let field = crate::hir_facts::FieldContext::for_curve(Curve::Bn254);
            let facts = crate::hir_facts::analyze(&lifted.hir, &cfg, &field, None).unwrap();
            assert_eq!(
                ComponentQueries::require_linear_caller_path(facts.cfg(), cfg.entry(), cfg.exit()),
                expected
            );
        }
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

#[cfg(test)]
#[path = "component/path_tests.rs"]
mod path_tests;

#[cfg(test)]
#[path = "component/binding_tests.rs"]
mod binding_tests;
