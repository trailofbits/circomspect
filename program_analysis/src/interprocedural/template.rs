use abstract_interpretation::graph::FlowGraph;
use parser::hir::{DefinitionRef, Effect, PortId, Template, TemplateId};
use parser::frontend::AssignmentOperator;

use crate::hir_cfg::{CfgNodeKind, DefinitionCfg, Origin};
use crate::hir_facts::{AccessHandle, AnalysisFacts, BodyWriteStatus, FieldValue, Incidence};

use crate::interprocedural::summary::certified;
use crate::interprocedural::cache::PortKey;
use crate::interprocedural::{
    CallContext, ContextEvidence, ProjectAnalysis, SummaryBlocker, SummaryFact,
};

/// Certified generated-constraint relation for one declared template port.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PortSummary {
    context: CallContext,
    port: PortId,
    indices: Vec<usize>,
    incidence: Incidence,
    fixed_value: Option<FieldValue>,
}

impl PortSummary {
    #[must_use]
    pub fn context(&self) -> &CallContext {
        &self.context
    }

    #[must_use]
    pub fn port(&self) -> PortId {
        self.port
    }

    #[must_use]
    pub fn indices(&self) -> &[usize] {
        &self.indices
    }

    #[must_use]
    pub fn incidence(&self) -> Incidence {
        self.incidence
    }

    #[must_use]
    pub fn fixed_value(&self) -> Option<&FieldValue> {
        self.fixed_value.as_ref()
    }
}

/// Whether a witness write also generated a constraint.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WitnessProvenance {
    WitnessOnly,
    GeneratedConstraint,
}

/// A reachable witness write with its checked HIR origin and operator semantics.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WitnessSite {
    origin: Origin,
    provenance: WitnessProvenance,
}

impl WitnessSite {
    #[must_use]
    pub fn origin(&self) -> Origin {
        self.origin
    }

    #[must_use]
    pub fn provenance(&self) -> WitnessProvenance {
        self.provenance
    }
}

/// Declared template-port summaries, reads, and witness queries for one session.
pub struct TemplateQueries<'session, 'hir> {
    pub(super) analysis: &'session ProjectAnalysis<'hir>,
}

impl TemplateQueries<'_, '_> {
    fn checked_port_key(
        &self,
        id: TemplateId,
        context: &CallContext,
        port: PortId,
        indices: &[usize],
    ) -> Result<PortKey, SummaryBlocker> {
        let template = self.analysis.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
        if context.definition() != DefinitionRef::Template(id) {
            return Err(SummaryBlocker::WrongContext);
        }
        self.analysis.contexts().check_context(context)?;
        if !template.ports.contains(&port) {
            return Err(SummaryBlocker::ForeignDefinition);
        }
        Ok(PortKey::new(context, port, indices))
    }

    /// Generated-constraint facts for one scalar declared port in this context.
    #[must_use]
    pub fn template_port(
        &self,
        id: TemplateId,
        context: &CallContext,
        port: PortId,
    ) -> SummaryFact<PortSummary> {
        self.template_port_at(id, context, port, &[])
    }

    /// Generated-constraint facts for one exact declared port element.
    #[must_use]
    pub fn template_port_at(
        &self,
        id: TemplateId,
        context: &CallContext,
        port: PortId,
        indices: &[usize],
    ) -> SummaryFact<PortSummary> {
        let key = match self.checked_port_key(id, context, port, indices) {
            Ok(key) => key,
            Err(blocker) => return SummaryFact::from_result(Err(blocker)),
        };
        self.analysis.caches.ports.get_or_compute(key, || {
            SummaryFact::from_result(self.with_local_template(id, context, |_, _, facts| {
                port_summary(facts, context, port, indices)
            }))
        })
    }

    /// Certify port constraints in a provider-issued, source-valid template scope.
    ///
    /// Every reachable signal read must have proven initialization, and generated
    /// constraints must have supported source form. Constructors require validated
    /// leaf children without input ports; deeper or unbound execution abstains.
    /// Called input ports additionally require a complete single-child main scope
    /// with witness-only input bindings and no related parent constraints. The
    /// supplied facts retain their original analysis budget and specialization.
    #[must_use]
    pub fn template_port_for_evidence(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        port: PortId,
        indices: &[usize],
    ) -> SummaryFact<PortSummary> {
        if let crate::interprocedural::ContextOrigin::Call(_) = evidence.origin() {
            return SummaryFact::from_result(
                self.analysis.called_input_port(facts, evidence, port, indices),
            );
        }
        let result = self
            .analysis
            .execution()
            .check_template_incidence_scope(facts, evidence)
            .and_then(|()| port_summary(facts, evidence.context(), port, indices));
        SummaryFact::from_result(result)
    }

    /// Whether this declared port is read in the template's reachable local body.
    #[must_use]
    pub fn template_port_read(
        &self,
        id: TemplateId,
        context: &CallContext,
        port: PortId,
    ) -> SummaryFact<bool> {
        let key = match self.checked_port_key(id, context, port, &[]) {
            Ok(key) => key,
            Err(blocker) => return SummaryFact::from_result(Err(blocker)),
        };
        self.analysis.caches.reads.get_or_compute(key, || {
            SummaryFact::from_result(self.with_local_template(id, context, |_, _, facts| {
                let handle = facts
                    .port_handle(port, &[])
                    .map_err(|error| SummaryBlocker::LocalAnalysis(error.to_string()))?;
                require_no_repeated_body_write(facts, &handle)?;
                let read = facts.read_handle(&handle);
                Ok(*certified(&read)?)
            }))
        })
    }

    /// Source sites for reachable witness writes to one exact scalar port.
    #[must_use]
    pub fn template_port_witnesses(
        &self,
        id: TemplateId,
        context: &CallContext,
        port: PortId,
    ) -> SummaryFact<Vec<WitnessSite>> {
        let key = match self.checked_port_key(id, context, port, &[]) {
            Ok(key) => key,
            Err(blocker) => return SummaryFact::from_result(Err(blocker)),
        };
        self.analysis.caches.witnesses.get_or_compute(key, || {
            SummaryFact::from_result(self.with_local_template(id, context, |_, cfg, facts| {
                let handle = facts
                    .port_handle(port, &[])
                    .map_err(|error| SummaryBlocker::LocalAnalysis(error.to_string()))?;
                require_no_repeated_body_write(facts, &handle)?;
                let symbol = self
                    .analysis
                    .hir()
                    .port(port)
                    .map(|item| item.symbol)
                    .ok_or(SummaryBlocker::ForeignDefinition)?;
                let mut sites = Vec::new();
                for id in cfg.nodes() {
                    let Some(node) = cfg.node(*id) else {
                        return Err(SummaryBlocker::LocalAnalysis("missing witness node".into()));
                    };
                    let relevant = match &node.kind {
                        CfgNodeKind::Witness { target, .. }
                        | CfgNodeKind::OpaqueAssignment { target, .. } => target.root == symbol,
                        CfgNodeKind::Opaque(_) => true,
                        _ => false,
                    };
                    if !relevant || !*certified(&facts.reachable_node(*id))? {
                        continue;
                    }
                    match &node.kind {
                        CfgNodeKind::Witness { target, .. } if target.steps.is_empty() => {
                            let origin = node.origin.ok_or(SummaryBlocker::LocalAnalysis(
                                "missing witness origin".into(),
                            ))?;
                            sites.push(self.witness_site(origin)?);
                        }
                        CfgNodeKind::Witness { .. } => {
                            return Err(SummaryBlocker::UnsupportedContext)
                        }
                        CfgNodeKind::OpaqueAssignment { .. } | CfgNodeKind::Opaque(_) => {
                            return Err(SummaryBlocker::ExternalSummary);
                        }
                        _ => {}
                    }
                }
                Ok(sites)
            }))
        })
    }

    fn witness_site(&self, origin: Origin) -> Result<WitnessSite, SummaryBlocker> {
        let effect = self
            .analysis
            .hir()
            .block(origin.block)
            .and_then(|block| block.effects.get(origin.effect_index))
            .ok_or(SummaryBlocker::LocalAnalysis("missing witness effect".into()))?;
        let provenance = match effect {
            Effect::WitnessAssignment { .. }
            | Effect::OpaqueAssignment {
                operator: AssignmentOperator::Witness | AssignmentOperator::ReverseWitness,
                ..
            } => WitnessProvenance::WitnessOnly,
            Effect::ConstraintAssignment { .. }
            | Effect::OpaqueAssignment {
                operator: AssignmentOperator::Constraint | AssignmentOperator::ReverseConstraint,
                ..
            } => WitnessProvenance::GeneratedConstraint,
            _ => return Err(SummaryBlocker::LocalAnalysis("mismatched witness origin".into())),
        };
        Ok(WitnessSite { origin, provenance })
    }

    pub(super) fn with_local_template<T, F>(
        &self,
        id: TemplateId,
        context: &CallContext,
        work: F,
    ) -> Result<T, SummaryBlocker>
    where
        F: FnOnce(&Template, &DefinitionCfg, &AnalysisFacts<'_>) -> Result<T, SummaryBlocker>,
    {
        let template = self.analysis.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
        if context.definition() != DefinitionRef::Template(id) {
            return Err(SummaryBlocker::WrongContext);
        }
        self.analysis.contexts().check_context(context)?;
        if template.custom || template.external {
            return Err(SummaryBlocker::ExternalSummary);
        }
        let parameters = context.scalar_seeds(&template.parameters);
        self.analysis.functions().with_refined_facts(context, &parameters, |cfg, facts| {
            if let Some(failure) =
                self.analysis.contexts().invalid_value_use(&template.parameters, context, facts)
            {
                return Err(failure.summary_blocker());
            }

            if self.analysis.execution().definition_definitely_fails(facts)? {
                return Err(SummaryBlocker::UnsupportedContext);
            }
            work(template, cfg, facts)
        })
    }
}

fn require_no_repeated_body_write(
    facts: &AnalysisFacts<'_>,
    handle: &AccessHandle,
) -> Result<(), SummaryBlocker> {
    let status = facts.body_write_status_handle(handle);
    match certified(&status)? {
        BodyWriteStatus::NoRepeat(_) => Ok(()),
        BodyWriteStatus::DefinitelyRepeated(_) => Err(SummaryBlocker::UnsupportedContext),
    }
}

pub(super) fn port_summary(
    facts: &AnalysisFacts<'_>,
    context: &CallContext,
    port: PortId,
    indices: &[usize],
) -> Result<PortSummary, SummaryBlocker> {
    let handle = facts
        .port_handle(port, indices)
        .map_err(|error| SummaryBlocker::LocalAnalysis(error.to_string()))?;
    require_no_repeated_body_write(facts, &handle)?;
    let incidence = facts.incidence_handle(&handle);
    let fixed = facts.constraint_fixed_handle(&handle);
    Ok(PortSummary {
        context: context.clone(),
        port,
        indices: indices.to_vec(),
        incidence: *certified(&incidence)?,
        fixed_value: certified(&fixed)?.clone(),
    })
}

#[cfg(test)]
mod tests {
    use abstract_interpretation::graph::FlowGraph;
    use parser::frontend::{parse_source, LoadedProject, SourceFile, SourceId, Version, VersionPolicy};
    use parser::hir::{lift_project, DefinitionRef};
    use program_structure::constants::Curve;

    use crate::hir_cfg::CfgNodeKind;
    use crate::interprocedural::{ProjectAnalysis, SummaryBlocker, WitnessProvenance};

    #[test]
    fn template_callback_returns_owned_witness_provenance() {
        let source = "template T(){signal output y;y<--7;}";
        let policy = VersionPolicy::new(Version::new(2, 2, 3));
        let id = SourceId::new(0);
        let loaded = LoadedProject {
            policy,
            diagnostics: Vec::new(),
            files: vec![SourceFile {
                id,
                path: "template-view.circom".into(),
                text: source.into(),
                outcome: parse_source(id, source, policy),
            }],
        };
        let lifted = lift_project(&loaded);
        let analysis = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let DefinitionRef::Template(template) = lifted.hir.definition("T").unwrap() else {
            panic!("template T")
        };
        let context =
            analysis.contexts().symbolic_context_for(DefinitionRef::Template(template)).unwrap();
        let provenance = analysis
            .templates()
            .with_local_template(template, &context, |_, cfg, _| {
                for id in cfg.nodes() {
                    let node = cfg.node(*id).unwrap();
                    if let CfgNodeKind::Witness { .. } = &node.kind {
                        return Ok(analysis
                            .templates()
                            .witness_site(node.origin.unwrap())?
                            .provenance());
                    }
                }
                Err(SummaryBlocker::IncompleteDefinition)
            })
            .unwrap();
        assert_eq!(provenance, WitnessProvenance::WitnessOnly);
    }
}
