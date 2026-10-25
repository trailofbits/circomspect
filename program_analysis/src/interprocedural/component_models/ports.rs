//! Scoped aliases from provider-checked component ports to child-local storage.

use std::collections::BTreeMap;

use crate::hir_facts::{AccessKey, AnalysisFacts};
use crate::interprocedural::input_relation::{CheckedInputSchema, InputPortElement, ReadyInstanceAtUse};
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
    input_aliases: BTreeMap<AccessKey, AccessKey>,
}

impl ValidatedComponentPorts {
    pub(super) fn new(
        caller: &AnalysisFacts<'_>,
        child: &AnalysisFacts<'_>,
        instance: &EnumeratedComponentInstance,
        ready: &ReadyInstanceAtUse,
    ) -> Result<Self, SummaryBlocker> {
        let (evidence, outputs) = checked_outputs(caller, child, instance)?;
        let mut inputs = BTreeMap::new();
        for port in ready.bindings().keys() {
            let handle = child
                .port_handle(port.port(), port.indices())
                .map_err(|_| SummaryBlocker::UnsupportedContext)?;
            inputs.insert(port.clone(), certified(&child.exact_handle_key(&handle))?.clone());
        }
        Ok(Self { evidence, outputs, inputs, input_aliases: BTreeMap::new() })
    }

    pub(in crate::interprocedural) fn from_schema(
        caller: &AnalysisFacts<'_>,
        child: &AnalysisFacts<'_>,
        instance: &EnumeratedComponentInstance,
        schema: CheckedInputSchema,
    ) -> Result<Self, SummaryBlocker> {
        let inputs = schema.into_elements(caller, child, instance)?;
        let (evidence, outputs) = checked_outputs(caller, child, instance)?;
        let mut ports =
            Self { evidence, outputs, inputs: BTreeMap::new(), input_aliases: BTreeMap::new() };
        for (element, alias) in inputs {
            ports.inputs.insert(element, alias.callee.clone());
            ports.input_aliases.insert(alias.caller, alias.callee);
        }
        Ok(ports)
    }

    pub(crate) fn contains_access(&self, key: &AccessKey) -> bool {
        self.contains_output(key) || self.input_aliases.contains_key(key)
    }

    pub(in crate::interprocedural) fn input_elements(
        &self,
    ) -> impl Iterator<Item = &InputPortElement> {
        self.inputs.keys()
    }

    pub(in crate::interprocedural) fn input_element(
        &self,
        caller: &AccessKey,
    ) -> Option<&InputPortElement> {
        let child = self.input_aliases.get(caller)?;
        self.inputs.iter().find_map(|(element, key)| (key == child).then_some(element))
    }

    pub(crate) fn evidence(&self) -> &ContextEvidence {
        &self.evidence
    }

    pub(crate) fn contains_output(&self, key: &AccessKey) -> bool {
        self.outputs.iter().any(|output| &output.caller == key)
    }

    pub(in crate::interprocedural) fn child_key(&self, parent: &AccessKey) -> Option<&AccessKey> {
        self.outputs.iter().find_map(|output| (output.caller == *parent).then_some(&output.callee))
    }

    pub(in crate::interprocedural) fn parent_key(&self, child: &AccessKey) -> Option<&AccessKey> {
        self.outputs.iter().find_map(|output| (&output.callee == child).then_some(&output.caller))
    }

    pub(in crate::interprocedural) fn input_key(
        &self,
        port: &InputPortElement,
    ) -> Option<&AccessKey> {
        self.inputs.get(port)
    }
}

fn checked_outputs(
    caller: &AnalysisFacts<'_>,
    child: &AnalysisFacts<'_>,
    instance: &EnumeratedComponentInstance,
) -> Result<(ContextEvidence, Vec<CheckedOutput>), SummaryBlocker> {
    let mut outputs = Vec::new();
    for output in &instance.outputs {
        let applied = output.applied_port();
        let (port, indices) =
            applied.handle().output_port().ok_or(SummaryBlocker::WrongInstance)?;
        let handle =
            child.port_handle(port, &indices).map_err(|_| SummaryBlocker::UnsupportedContext)?;
        outputs.push(CheckedOutput {
            caller: certified(&caller.applied_component_key(applied))?.clone(),
            callee: certified(&child.exact_handle_key(&handle))?.clone(),
            applied: applied.clone(),
        });
    }
    let first = outputs.first().ok_or(SummaryBlocker::WrongInstance)?;
    let evidence = first.applied.caller_evidence().clone();
    Ok((evidence, outputs))
}
