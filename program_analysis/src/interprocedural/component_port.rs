//! Output handles checked in the caller's instance and callee's port contexts.

use parser::hir::{AccessStep, ArrayIndex, DefinitionRef, PortId};

use crate::hir_cfg::build_cfg;
use crate::hir_facts::{AccessHandle, AnalysisFacts};
use crate::interprocedural::component::binding::CheckedCallContext;
use crate::interprocedural::{
    AnalyzeEvidenceError, AppliedComponentPort, ContextEvidence, ComponentQueries, ReachableCall,
    SummaryBlocker, SummaryFact,
};

#[derive(Clone, Copy)]
pub(super) struct LocalOutputPort<'a, 'hir> {
    pub facts: &'a AnalysisFacts<'hir>,
    pub handle: &'a AccessHandle,
}

impl ComponentQueries<'_, '_> {
    /// Bind a callee-local output handle to its exact source component call.
    ///
    /// Caller instance indices and callee port indices are checked in their own
    /// parameter contexts. A local handle from another scope, project, or curve
    /// is rejected. This does not establish input readiness or caller closure.
    pub fn apply_component_local_output(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
        call: &ReachableCall<'_>,
        local: &AccessHandle,
    ) -> SummaryFact<AppliedComponentPort> {
        let result =
            CheckedCallContext::new(self.analysis, facts, caller, call).and_then(|context| {
                context.with_port_facts(|child| {
                    context.apply_local_port(LocalOutputPort { facts: child, handle: local })
                })
            });
        SummaryFact::from_result(result)
    }

    /// Bind the first output element using callee-checked port dimensions.
    ///
    /// This issues the same applied-port certificate as a local output handle,
    /// while keeping parameterized child dimensions in the child's context.
    pub fn apply_component_first_output(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
        call: &ReachableCall<'_>,
        output: PortId,
    ) -> SummaryFact<AppliedComponentPort> {
        let result =
            CheckedCallContext::new(self.analysis, facts, caller, call).and_then(|context| {
                context.with_port_facts(|child| {
                    let handle = child
                        .port_handle(output, &[0])
                        .map_err(|_| SummaryBlocker::UnsupportedContext)?;
                    context.apply_local_port(LocalOutputPort { facts: child, handle: &handle })
                })
            });
        SummaryFact::from_result(result)
    }

    pub(super) fn with_component_port_facts<T>(
        &self,
        callee: &ContextEvidence,
        work: impl FnOnce(&AnalysisFacts<'_>) -> Result<T, SummaryBlocker>,
    ) -> Result<T, SummaryBlocker> {
        let DefinitionRef::Template(_) = callee.context().definition() else {
            return Err(SummaryBlocker::WrongInstance);
        };
        let cfg = build_cfg(self.analysis.hir(), callee.context().definition())
            .map_err(|_| SummaryBlocker::IncompleteDefinition)?;
        let facts =
            self.analysis.contexts().analyze_for_evidence(&cfg, callee, None).map_err(|error| {
                match error {
                    AnalyzeEvidenceError::Blocked(blocker) => blocker,
                    AnalyzeEvidenceError::InvalidAssignment { .. }
                    | AnalyzeEvidenceError::InvalidValueUse { .. } => {
                        SummaryBlocker::IncompleteDefinition
                    }
                }
            })?;
        self.analysis.execution().check_call_execution_scope(&facts, callee)?;
        work(&facts)
    }

    pub(super) fn local_output_key(
        &self,
        handle: &AccessHandle,
    ) -> Result<(PortId, Vec<usize>), SummaryBlocker> {
        if handle.component().is_some() || handle.path().root != handle.path().terminal {
            return Err(SummaryBlocker::WrongInstance);
        }
        let port = self
            .analysis
            .hir()
            .ports()
            .iter()
            .find(|port| port.symbol == handle.path().root)
            .ok_or(SummaryBlocker::ForeignDefinition)?;
        let mut indices = Vec::new();
        for step in &handle.path().steps {
            match step {
                AccessStep::Index { index: ArrayIndex::Constant(value), .. } => {
                    indices.push(value.parse().map_err(|_| SummaryBlocker::UnsupportedContext)?);
                }
                AccessStep::Index { index: ArrayIndex::Symbolic(_), .. }
                | AccessStep::Port { .. }
                | AccessStep::Tag { .. } => {
                    return Err(SummaryBlocker::UnsupportedContext);
                }
            }
        }
        Ok((port.id, indices))
    }
}
