use abstract_interpretation::graph::FlowGraph;
use parser::hir::{DefinitionRef, Effect, PortId, Template, TemplateId};

use crate::hir_cfg::{build_cfg, CfgNodeKind, DefinitionCfg, Origin};
use crate::hir_facts::{
    analyze_with_scalar_parameters, AnalysisFacts, FieldContext, FieldValue, Incidence,
};

use super::summary::certified;
use super::{CallContext, ProjectSummaries, SummaryBlocker, SummaryFact};

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

impl ProjectSummaries<'_> {
    /// Generated-constraint facts for one scalar declared port in this context.
    pub fn template_port(
        &self,
        id: TemplateId,
        context: &CallContext,
        port: PortId,
    ) -> SummaryFact<PortSummary> {
        self.template_port_at(id, context, port, &[])
    }

    /// Generated-constraint facts for one exact declared port element.
    pub fn template_port_at(
        &self,
        id: TemplateId,
        context: &CallContext,
        port: PortId,
        indices: &[usize],
    ) -> SummaryFact<PortSummary> {
        SummaryFact::from_result(self.with_local_template(id, context, |template, _, facts| {
            if !template.ports.contains(&port) {
                return Err(SummaryBlocker::ForeignDefinition);
            }
            let handle = facts
                .port_handle(port, indices)
                .map_err(|error| SummaryBlocker::LocalAnalysis(error.to_string()))?;
            let incidence = facts.incidence_handle(&handle);
            let fixed = facts.constraint_fixed_handle(&handle);
            Ok(PortSummary {
                context: context.clone(),
                port,
                indices: indices.to_vec(),
                incidence: *certified(&incidence)?,
                fixed_value: certified(&fixed)?.clone(),
            })
        }))
    }

    /// Whether this declared port is read in the template's reachable local body.
    pub fn template_port_read(
        &self,
        id: TemplateId,
        context: &CallContext,
        port: PortId,
    ) -> SummaryFact<bool> {
        SummaryFact::from_result(self.with_local_template(id, context, |template, _, facts| {
            if !template.ports.contains(&port) {
                return Err(SummaryBlocker::ForeignDefinition);
            }
            let handle = facts
                .port_handle(port, &[])
                .map_err(|error| SummaryBlocker::LocalAnalysis(error.to_string()))?;
            let read = facts.read_handle(&handle);
            Ok(*certified(&read)?)
        }))
    }

    /// Source sites for reachable witness writes to one exact scalar port.
    pub fn template_port_witnesses(
        &self,
        id: TemplateId,
        context: &CallContext,
        port: PortId,
    ) -> SummaryFact<Vec<WitnessSite>> {
        SummaryFact::from_result(self.with_local_template(id, context, |template, cfg, facts| {
            if !template.ports.contains(&port) {
                return Err(SummaryBlocker::ForeignDefinition);
            }
            facts
                .port_handle(port, &[])
                .map_err(|error| SummaryBlocker::LocalAnalysis(error.to_string()))?;
            let symbol = self
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
                    CfgNodeKind::Witness { .. } => return Err(SummaryBlocker::UnsupportedContext),
                    CfgNodeKind::OpaqueAssignment { .. } | CfgNodeKind::Opaque(_) => {
                        return Err(SummaryBlocker::ExternalSummary);
                    }
                    _ => {}
                }
            }
            Ok(sites)
        }))
    }

    fn witness_site(&self, origin: Origin) -> Result<WitnessSite, SummaryBlocker> {
        let effect = self
            .hir()
            .block(origin.block)
            .and_then(|block| block.effects.get(origin.effect_index))
            .ok_or(SummaryBlocker::LocalAnalysis("missing witness effect".into()))?;
        let provenance = if let Effect::WitnessAssignment { .. } = effect {
            WitnessProvenance::WitnessOnly
        } else if let Effect::ConstraintAssignment { .. } = effect {
            WitnessProvenance::GeneratedConstraint
        } else {
            return Err(SummaryBlocker::LocalAnalysis("mismatched witness origin".into()));
        };
        Ok(WitnessSite { origin, provenance })
    }

    fn with_local_template<T>(
        &self,
        id: TemplateId,
        context: &CallContext,
        work: impl FnOnce(&Template, &DefinitionCfg, &AnalysisFacts<'_>) -> Result<T, SummaryBlocker>,
    ) -> Result<T, SummaryBlocker> {
        let template = self.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
        if context.definition() != DefinitionRef::Template(id) {
            return Err(SummaryBlocker::WrongContext);
        }
        self.check_context(context)?;
        if template.custom || template.external {
            return Err(SummaryBlocker::ExternalSummary);
        }
        let parameters = context.scalar_seeds(&template.parameters)?;
        let cfg = build_cfg(self.hir(), DefinitionRef::Template(id))
            .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
        let field = FieldContext::for_curve(self.curve().clone());
        let facts = analyze_with_scalar_parameters(self.hir(), &cfg, &field, parameters, None)
            .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
        work(template, &cfg, &facts)
    }
}
