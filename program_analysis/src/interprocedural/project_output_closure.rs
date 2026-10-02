//! Closed use of exact output paths across instantiated template scopes.

use std::collections::BTreeSet;

use parser::hir::{DefinitionRef, TemplateId};
use parser::new_frontend::PortDirection;

use crate::hir_cfg::build_cfg;
use crate::hir_facts::AnalysisFacts;
use crate::interprocedural::constructor_readiness::{CompletedChild, CompletedTemplate};
use crate::interprocedural::input_relation::ready_instance_at_use;
use crate::interprocedural::output_enumeration::EnumeratedComponentInstance;
use crate::interprocedural::project_use::{ProjectInstanceStep, ProjectOutputEvidence};
use crate::interprocedural::{
    CallContext, ContextEvidence, ProjectOutputStatus, ProjectOutputUse, ProjectSummaries,
    SummaryBlocker, SummaryFact,
};

const MAX_PROJECT_UNITS: usize = 256;

struct Closure {
    main: ContextEvidence,
    active: BTreeSet<CallContext>,
    path: Vec<ProjectInstanceStep>,
    used: usize,
    outputs: Vec<ProjectOutputUse>,
}

impl Closure {
    fn new(main: &ContextEvidence) -> Self {
        Self {
            main: main.clone(),
            active: BTreeSet::new(),
            path: Vec::new(),
            used: 0,
            outputs: Vec::new(),
        }
    }

    fn reserve(&mut self, amount: usize) -> Result<(), SummaryBlocker> {
        let Some(next) = self.used.checked_add(amount) else {
            return Err(SummaryBlocker::ContextBudget);
        };
        if next > MAX_PROJECT_UNITS {
            return Err(SummaryBlocker::ContextBudget);
        }
        self.used = next;
        Ok(())
    }

    fn remaining(&self) -> usize {
        MAX_PROJECT_UNITS - self.used
    }
}

impl ProjectSummaries<'_> {
    /// Certify all exact component-output uses under one closed instantiated main.
    ///
    /// Every returned negative use is bound to a checked instance chain. Missing
    /// source, calls, shapes, execution, input readiness, or analysis budget makes
    /// the whole negative closure unavailable. A local positive read remains
    /// independently available through `caller_output_read`.
    #[must_use]
    pub fn closed_project_output_uses(
        &self,
        facts: &AnalysisFacts<'_>,
        main: &ContextEvidence,
    ) -> SummaryFact<Vec<ProjectOutputUse>> {
        SummaryFact::from_result(self.closed_project_uses(facts, main))
    }

    fn closed_project_uses(
        &self,
        facts: &AnalysisFacts<'_>,
        main: &ContextEvidence,
    ) -> Result<Vec<ProjectOutputUse>, SummaryBlocker> {
        self.check_main_root(facts, main)?;
        let mut closure = Closure::new(main);
        self.visit_scope(facts, main, &mut closure)?;
        Ok(closure.outputs)
    }

    fn visit_scope(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        closure: &mut Closure,
    ) -> Result<CompletedTemplate, SummaryBlocker> {
        if !closure.active.insert(evidence.context().clone()) {
            return Err(SummaryBlocker::RecursiveCycle);
        }
        let result = self.visit_scope_body(facts, evidence, closure);
        closure.active.remove(evidence.context());
        result
    }

    fn visit_scope_body(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        closure: &mut Closure,
    ) -> Result<CompletedTemplate, SummaryBlocker> {
        self.check_facts_for_evidence(facts, evidence)?;
        self.validated_definition(facts)?;
        self.check_warning_execution_scope(facts, evidence)?;
        self.check_template_execution(facts.cfg(), facts)?;
        self.check_parent_components_complete(facts)?;
        let mut children = Vec::new();
        self.visit_component_calls(facts, evidence, |call| {
            closure.reserve(1)?;
            let instance = self.enumerate_call(facts, evidence, call, closure.remaining())?;
            closure.reserve(instance.outputs.len())?;
            children.push(self.visit_instance(facts, evidence, &instance, closure)?);
            Ok(())
        })?;
        self.completed_project_template(facts, evidence, &children)
    }

    fn visit_instance(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
        instance: &EnumeratedComponentInstance,
        closure: &mut Closure,
    ) -> Result<CompletedChild, SummaryBlocker> {
        let DefinitionRef::Template(child) = instance.callee.context().definition() else {
            return Err(SummaryBlocker::WrongInstance);
        };
        self.check_instance_inputs(facts, instance, child)?;
        closure.path.push(ProjectInstanceStep::new(
            instance.site,
            instance.target.clone(),
            instance.indices.clone(),
            instance.callee.clone(),
        ));
        let result = self.visit_instance_body(facts, instance, child, closure);
        closure.path.pop();
        self.completed_project_child(facts, caller, instance, result?)
    }

    fn visit_instance_body(
        &self,
        facts: &AnalysisFacts<'_>,
        instance: &EnumeratedComponentInstance,
        child: TemplateId,
        closure: &mut Closure,
    ) -> Result<CompletedTemplate, SummaryBlocker> {
        for output in &instance.outputs {
            self.record_output(facts, output, child, closure)?;
        }
        let cfg = build_cfg(self.hir(), DefinitionRef::Template(child))
            .map_err(|_| SummaryBlocker::IncompleteDefinition)?;
        let child_facts = self.analyze_for_evidence(&cfg, &instance.callee, None).map_err(
            |error| match error {
                crate::interprocedural::AnalyzeEvidenceError::Blocked(blocker) => blocker,
                crate::interprocedural::AnalyzeEvidenceError::InvalidAssignment { .. }
                | crate::interprocedural::AnalyzeEvidenceError::InvalidValueUse { .. } => {
                    SummaryBlocker::IncompleteDefinition
                }
            },
        )?;
        self.visit_scope(&child_facts, &instance.callee, closure)
    }

    fn check_instance_inputs(
        &self,
        facts: &AnalysisFacts<'_>,
        instance: &EnumeratedComponentInstance,
        child: TemplateId,
    ) -> Result<(), SummaryBlocker> {
        let template = self.hir().template(child).ok_or(SummaryBlocker::ForeignDefinition)?;
        let mut has_inputs = false;
        for id in &template.ports {
            let port = self.hir().port(*id).ok_or(SummaryBlocker::ForeignDefinition)?;
            if port.direction == Some(PortDirection::Input) {
                has_inputs = true;
            }
        }
        if !has_inputs {
            return Ok(());
        }
        let output = instance.outputs.first().ok_or(SummaryBlocker::UnsupportedContext)?;
        ready_instance_at_use(facts, output.applied_port(), child)?;
        Ok(())
    }

    fn record_output(
        &self,
        facts: &AnalysisFacts<'_>,
        output: &crate::interprocedural::EnumeratedComponentOutput,
        child: TemplateId,
        closure: &mut Closure,
    ) -> Result<(), SummaryBlocker> {
        let applied = output.applied_port();
        let local = self.local_output_use_result(facts, applied)?;
        let use_state = match local {
            crate::interprocedural::component::LocalOutputUse::Read(sites) => {
                crate::interprocedural::component::LocalOutputUse::Read(sites)
            }
            crate::interprocedural::component::LocalOutputUse::NoLocalRead => {
                self.child_output_use(child, applied)?
            }
        };
        let (status, reads) = match use_state {
            crate::interprocedural::component::LocalOutputUse::Read(sites) => {
                (ProjectOutputStatus::Read, sites)
            }
            crate::interprocedural::component::LocalOutputUse::NoLocalRead => {
                (ProjectOutputStatus::Unused, Vec::new())
            }
        };
        let evidence =
            ProjectOutputEvidence { reads, span: output.source_span(), path: closure.path.clone() };
        closure.outputs.push(ProjectOutputUse::component(
            closure.main.clone(),
            applied.clone(),
            status,
            evidence,
        ));
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::interprocedural::project_output_closure::Closure;
    use crate::interprocedural::ProjectSummaries;
    use parser::hir::lift_project;
    use parser::new_frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;
    use crate::interprocedural::SummaryBlocker;

    #[test]
    fn outputless_instances_still_exhaust_the_closure_budget() {
        let directory = std::env::temp_dir().join("circomspect-project-closure-budget");
        std::fs::create_dir_all(&directory).unwrap();
        let file = directory.join("case.circom");
        std::fs::write(&file, "template Main(){} component main=Main();").unwrap();
        let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("Main").unwrap();
        let main = provider.symbolic_root(definition).unwrap();
        let mut closure = Closure::new(&main);
        for _ in 0..256 {
            assert!(closure.reserve(1).is_ok());
        }
        assert_eq!(closure.reserve(1), Err(SummaryBlocker::ContextBudget));
    }
}
