//! Exact constructor and port schemas for the bounded comparator closure.

use parser::hir::{DefinitionRef, PortId, PortSchema};
use parser::new_frontend::PortDirection;

use crate::hir_facts::{AccessHandle, AnalysisFacts};
use crate::interprocedural::output_enumeration::EnumeratedComponentInstance;
use crate::interprocedural::{ContextEvidence, ProjectSummaries, SummaryBlocker};

impl ProjectSummaries<'_> {
    pub(super) fn comparator_child(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<EnumeratedComponentInstance, SummaryBlocker> {
        self.check_parent_components_complete(facts)?;
        let mut child = None;
        self.visit_component_calls(facts, evidence, |call| {
            if child.is_some() {
                return Err(SummaryBlocker::UnsupportedContext);
            }
            child = Some(self.enumerate_call(facts, evidence, call, 512)?);
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
    let symbol = facts.hir().port(port).ok_or(SummaryBlocker::ForeignDefinition)?.symbol;
    let dimensions =
        facts.checked_symbol_dimensions(symbol).map_err(|_| SummaryBlocker::UnsupportedContext)?;
    let [width] = dimensions.as_slice() else { return Err(SummaryBlocker::UnsupportedContext) };
    if *width == 0 || *width > 512 {
        return Err(SummaryBlocker::UnsupportedContext);
    }
    let mut handles = Vec::new();
    for index in 0..*width {
        handles.push(
            facts.port_handle(port, &[index]).map_err(|_| SummaryBlocker::UnsupportedContext)?,
        );
    }
    Ok(handles)
}
