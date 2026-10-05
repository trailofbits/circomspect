//! Scoped aliases from provider-checked component ports to child-local storage.

use std::collections::BTreeMap;

use crate::hir_facts::{AccessKey, AnalysisFacts};
use crate::interprocedural::input_relation::{InputPortElement, ReadyInstanceAtUse};
use crate::interprocedural::output_enumeration::EnumeratedComponentInstance;
use crate::interprocedural::summary::certified;
use crate::interprocedural::{AppliedComponentPort, ContextEvidence, SummaryBlocker};

struct CheckedOutput {
    applied: AppliedComponentPort,
    caller: AccessKey,
    callee: AccessKey,
}

/// Exact aliases issued from caller instance bounds and callee port bounds.
/// The fields are private so a source path alone cannot authorize a bounds exemption.
pub(crate) struct ValidatedComponentPorts {
    evidence: ContextEvidence,
    outputs: Vec<CheckedOutput>,
    inputs: BTreeMap<InputPortElement, AccessKey>,
}

impl ValidatedComponentPorts {
    pub(super) fn new(
        caller: &AnalysisFacts<'_>,
        child: &AnalysisFacts<'_>,
        instance: &EnumeratedComponentInstance,
        ready: &ReadyInstanceAtUse,
    ) -> Result<Self, SummaryBlocker> {
        let mut outputs = Vec::new();
        for output in &instance.outputs {
            let applied = output.applied_port();
            let (port, indices) =
                applied.handle().output_port().ok_or(SummaryBlocker::WrongInstance)?;
            let handle = child
                .port_handle(port, &indices)
                .map_err(|_| SummaryBlocker::UnsupportedContext)?;
            outputs.push(CheckedOutput {
                caller: certified(&caller.applied_component_key(applied))?.clone(),
                callee: certified(&child.exact_handle_key(&handle))?.clone(),
                applied: applied.clone(),
            });
        }
        let first = outputs.first().ok_or(SummaryBlocker::WrongInstance)?;
        let evidence = first.applied.caller_evidence().clone();
        let mut inputs = BTreeMap::new();
        for port in ready.bindings().keys() {
            let handle = child
                .port_handle(port.port(), port.indices())
                .map_err(|_| SummaryBlocker::UnsupportedContext)?;
            inputs.insert(port.clone(), certified(&child.exact_handle_key(&handle))?.clone());
        }
        Ok(Self { evidence, outputs, inputs })
    }

    pub(crate) fn evidence(&self) -> &ContextEvidence {
        &self.evidence
    }

    pub(crate) fn contains_output(&self, key: &AccessKey) -> bool {
        self.outputs.iter().any(|output| &output.caller == key)
    }

    pub(super) fn child_key(&self, parent: &AccessKey) -> Option<&AccessKey> {
        self.outputs.iter().find_map(|output| (output.caller == *parent).then_some(&output.callee))
    }

    pub(super) fn input_key(&self, port: &InputPortElement) -> Option<&AccessKey> {
        self.inputs.get(port)
    }
}
