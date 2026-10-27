//! Complete incoming scope for a witness-initialized leaf input divisor.

use parser::hir::PortId;
use parser::frontend::PortDirection;

use crate::hir_cfg::build_cfg;
use crate::hir_facts::{AnalysisFacts, Incidence, ProofBudget};
use crate::interprocedural::input_relation::{ready_witness_instance, WitnessInputValue};
use crate::interprocedural::output_enumeration::EnumeratedComponentInstance;
use crate::interprocedural::summary::certified;
use crate::interprocedural::template::port_summary;
use crate::interprocedural::{
    CallOwner, CallReachability, ContextEvidence, PortSummary, ProjectAnalysis, SummaryBlocker,
};

impl ProjectAnalysis<'_> {
    pub(super) fn called_input_port(
        &self,
        child: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        port: PortId,
        indices: &[usize],
    ) -> Result<PortSummary, SummaryBlocker> {
        self.contexts().check_facts_for_evidence(child, evidence)?;
        let schema = self.hir().port(port).ok_or(SummaryBlocker::ForeignDefinition)?;
        if schema.direction != Some(PortDirection::Input) || !indices.is_empty() {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        let summary = port_summary(child, evidence.context(), port, indices)?;
        if summary.incidence() != Incidence::Zero {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        let parent = self.direct_main_parent(evidence)?;
        let cfg = build_cfg(self.hir(), parent.context().definition())
            .map_err(|error| SummaryBlocker::LocalAnalysis(format!("caller CFG: {error:?}")))?;
        let facts = self
            .contexts()
            .analyze_for_evidence(&cfg, &parent, None)
            .map_err(|error| SummaryBlocker::LocalAnalysis(format!("caller facts: {error:?}")))?;
        self.check_model_main_root(&facts, &parent)?;
        let instance = self.sole_child_instance(&facts, &parent, evidence)?;
        let ready = ready_witness_instance(&facts, &parent, &instance)?;
        let completed = self.execution().completed_project_template(child, evidence, &[])?;
        let completed =
            self.execution().completed_witness_child(&facts, &instance, completed, &ready)?;
        self.execution().completed_project_template(
            &facts,
            &parent,
            std::slice::from_ref(&completed),
        )?;
        let constructors =
            self.execution().completed_constructor_reads(&facts, &parent, &[completed])?;
        let mut budget = ProofBudget::default();
        child.unique_generation_path(&mut budget).map_err(SummaryBlocker::LocalFacts)?;
        facts
            .unique_generation_path_with(&mut budget, &constructors)
            .map_err(SummaryBlocker::LocalFacts)?;
        let equations = facts.generated_equation_sites(&mut budget);
        let equations = certified(&equations)?;
        let binding = ready.binding(port).ok_or(SummaryBlocker::MissingInputBinding)?;
        if equations.keys().iter().any(|key| key.may_alias(&binding.target)) {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        match &binding.value {
            WitnessInputValue::Constant(_) => {}
            WitnessInputValue::ParentSignal(key) => {
                // Internal witness aliases require a transitive dependency certificate.
                let external = self.hir().ports().iter().any(|port| {
                    port.symbol == key.root && port.direction == Some(PortDirection::Input)
                });
                if !external || equations.keys().iter().any(|other| key.may_alias(other)) {
                    return Err(SummaryBlocker::UnsupportedContext);
                }
            }
        }
        Ok(summary)
    }

    fn direct_main_parent(
        &self,
        evidence: &ContextEvidence,
    ) -> Result<ContextEvidence, SummaryBlocker> {
        let [main, child] = evidence.call_path() else {
            return Err(SummaryBlocker::ExternalSummary);
        };
        let CallOwner::Main(index) = main.owner() else {
            return Err(SummaryBlocker::ExternalSummary);
        };
        if child.owner() != CallOwner::Definition(main.callee()) {
            return Err(SummaryBlocker::WrongContext);
        }
        let sites = self.graph().calls_from(CallOwner::Main(index));
        let [site] = sites.as_slice() else { return Err(SummaryBlocker::ForeignCall) };
        let CallReachability::Reachable(call) =
            self.graph().reachable_main_call(site.id(), self.hir())
        else {
            return Err(SummaryBlocker::ForeignCall);
        };
        self.contexts().main_evidence(&call)
    }

    fn sole_child_instance(
        &self,
        facts: &AnalysisFacts<'_>,
        parent: &ContextEvidence,
        child: &ContextEvidence,
    ) -> Result<EnumeratedComponentInstance, SummaryBlocker> {
        let mut instance = None;
        self.components().visit_component_calls(facts, parent, |call| {
            if instance.is_some() || self.contexts().call_evidence(call, facts, parent)? != *child {
                return Err(SummaryBlocker::UnsupportedContext);
            }
            instance = Some(self.components().enumerate_call(facts, parent, call, 256)?);
            Ok(())
        })?;
        instance.ok_or(SummaryBlocker::WrongInstance)
    }
}
