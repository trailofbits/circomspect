//! Exact constructor and port schemas for the bounded comparator closure.

use parser::hir::{DefinitionRef, PortId, PortSchema};
use parser::frontend::PortDirection;

use crate::hir_facts::{AccessHandle, AnalysisFacts};
use crate::interprocedural::comparator_range::ComparatorQuery;
use crate::interprocedural::output_enumeration::EnumeratedComponentInstance;
use crate::interprocedural::{ContextEvidence, SummaryBlocker};

impl ComparatorQuery<'_, '_> {
    pub(super) fn check_output(&self) -> Result<(), SummaryBlocker> {
        let facts = self.facts;
        let applied = self.applied;
        self.analysis.contexts().check_facts_for_evidence(facts, applied.caller_evidence())?;
        self.analysis.contexts().check_evidence(applied.callee_evidence())?;
        let DefinitionRef::Template(id) = applied.callee_evidence().context().definition() else {
            return Err(SummaryBlocker::WrongInstance);
        };
        let (port, indices) =
            applied.handle().output_port().ok_or(SummaryBlocker::WrongInstance)?;
        let template = self.analysis.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
        if !template.ports.contains(&port) {
            return Err(SummaryBlocker::WrongInstance);
        }
        let port = self.analysis.hir().port(port).ok_or(SummaryBlocker::ForeignDefinition)?;
        let symbol =
            self.analysis.hir().symbol(port.symbol).ok_or(SummaryBlocker::ForeignDefinition)?;
        if port.direction != Some(PortDirection::Output)
            || port.schema != PortSchema::Signal
            || symbol.rank != 0
            || !indices.is_empty()
        {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        Ok(())
    }

    pub(super) fn comparator_child(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<EnumeratedComponentInstance, SummaryBlocker> {
        self.analysis.check_parent_components_complete(facts)?;
        let mut child = None;
        self.analysis.components().visit_component_calls(facts, evidence, |call| {
            if child.is_some() {
                return Err(SummaryBlocker::UnsupportedContext);
            }
            child = Some(self.analysis.components().enumerate_call(facts, evidence, call, 512)?);
            Ok(())
        })?;
        child.ok_or(SummaryBlocker::UnsupportedContext)
    }
}

pub(super) fn bit_handles(facts: &AnalysisFacts<'_>) -> Result<Vec<AccessHandle>, SummaryBlocker> {
    let DefinitionRef::Template(id) = facts.definition() else {
        return Err(SummaryBlocker::WrongInstance);
    };
    let template = facts.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
    let mut output = None;
    for id in &template.ports {
        let port = facts.hir().port(*id).ok_or(SummaryBlocker::ForeignDefinition)?;
        if port.direction == Some(PortDirection::Output)
            && (port.schema != PortSchema::Signal || output.replace(port.id).is_some())
        {
            return Err(SummaryBlocker::UnsupportedContext);
        }
    }
    ordered_output_handles(facts, output.ok_or(SummaryBlocker::UnsupportedContext)?)
}

fn ordered_output_handles(
    facts: &AnalysisFacts<'_>,
    port: PortId,
) -> Result<Vec<AccessHandle>, SummaryBlocker> {
    let port = facts.hir().port(port).ok_or(SummaryBlocker::ForeignDefinition)?;
    facts.rank_one_port_handles(port, 512).map_err(|_| SummaryBlocker::UnsupportedContext)
}

#[cfg(test)]
mod tests;
