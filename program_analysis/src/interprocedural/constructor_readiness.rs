//! Provider-owned leaf constructor coverage for local signal-read validation.

use std::collections::BTreeSet;

use abstract_interpretation::graph::{FlowGraph, NodeId};
use parser::hir::{AccessPath, DefinitionRef, ExprId, ExprKind};
use parser::new_frontend::PortDirection;

use crate::hir_cfg::{build_cfg, CfgNodeKind};
use crate::hir_facts::{AnalysisFacts, InstanceRelation};
use crate::interprocedural::input_relation::{
    ready_enumerated_instance, ready_model_instance, ReadyInstanceAtUse,
};
use crate::interprocedural::{
    AppliedComponentPort, CallOwner, CallReachability, CallSiteId, ContextEvidence,
    ProjectSummaries, SummaryBlocker,
};
use crate::interprocedural::output_enumeration::EnumeratedComponentInstance;
use crate::interprocedural::summary::certified;

/// Constructors whose exact leaf children passed source, read, and generated-form checks.
/// This is local readiness coverage, not a successful-termination certificate.
pub(crate) struct ValidatedConstructorReads {
    evidence: ContextEvidence,
    calls: BTreeSet<ExprId>,
    outputs: Vec<ValidatedComponentOutputRead>,
}

#[derive(Clone)]
struct ValidatedComponentOutputRead {
    site: NodeId,
    path: AccessPath,
    applied: AppliedComponentPort,
}

impl ValidatedComponentOutputRead {
    fn matches(&self, facts: &AnalysisFacts<'_>, path: &AccessPath) -> bool {
        let Some(CfgNodeKind::Evaluate(expression)) =
            facts.cfg().node(self.site).map(|node| &node.kind)
        else {
            return false;
        };
        let Some(ExprKind::Access(source)) =
            facts.hir().expression(*expression).map(|expression| &expression.kind)
        else {
            return false;
        };
        self.path == *path
            && source == path
            && facts.reachable_node(self.site).certified() == Some(&true)
            && facts.handle_relation(self.applied.handle(), path) == InstanceRelation::Exact
    }
}

pub(super) struct CompletedTemplate {
    evidence: ContextEvidence,
}

enum ChildCompletion {
    ProjectOutput(CompletedTemplate),
    CompleteModels(CompletedTemplate),
}

pub(super) struct CompletedChild {
    caller: ContextEvidence,
    site: CallSiteId,
    indices: Vec<usize>,
    completed: CompletedTemplate,
    outputs: Vec<ValidatedComponentOutputRead>,
}

impl ValidatedConstructorReads {
    pub(crate) fn evidence(&self) -> &ContextEvidence {
        &self.evidence
    }

    pub(crate) fn contains(&self, expression: ExprId) -> bool {
        self.calls.contains(&expression)
    }

    /// The input relation has already checked every reachable matching
    /// `Evaluate` site in this caller's completed CFG. The same access may be
    /// visited again from its enclosing expression or effect by the generic
    /// read visitor; this capability covers those visits as well.
    pub(crate) fn allows_output(&self, facts: &AnalysisFacts<'_>, path: &AccessPath) -> bool {
        self.outputs.iter().any(|read| read.matches(facts, path))
    }
}

impl ProjectSummaries<'_> {
    pub(super) fn completed_project_child(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
        instance: &EnumeratedComponentInstance,
        completed: CompletedTemplate,
    ) -> Result<CompletedChild, SummaryBlocker> {
        self.complete_child(facts, caller, instance, ChildCompletion::ProjectOutput(completed))
            .map(|(child, _)| child)
    }

    pub(super) fn completed_model_child(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
        instance: &EnumeratedComponentInstance,
        completed: CompletedTemplate,
    ) -> Result<(CompletedChild, ReadyInstanceAtUse), SummaryBlocker> {
        self.complete_child(facts, caller, instance, ChildCompletion::CompleteModels(completed))
    }

    fn complete_child(
        &self,
        facts: &AnalysisFacts<'_>,
        caller: &ContextEvidence,
        instance: &EnumeratedComponentInstance,
        completion: ChildCompletion,
    ) -> Result<(CompletedChild, ReadyInstanceAtUse), SummaryBlocker> {
        self.check_facts_for_evidence(facts, caller)?;
        let (completed, ready) = match completion {
            ChildCompletion::ProjectOutput(completed) => {
                (completed, ready_enumerated_instance(facts, instance)?)
            }
            ChildCompletion::CompleteModels(completed) => {
                (completed, ready_model_instance(facts, instance)?)
            }
        };
        if completed.evidence != instance.callee {
            return Err(SummaryBlocker::WrongContext);
        }
        let site = self.graph().site(instance.site).ok_or(SummaryBlocker::ForeignCall)?;
        if site.owner != CallOwner::Definition(facts.definition()) {
            return Err(SummaryBlocker::ForeignCall);
        }
        let CallReachability::Reachable(call) = self.graph().reachable_call(instance.site, facts)
        else {
            return Err(SummaryBlocker::ForeignCall);
        };
        if self.call_evidence(&call, facts, caller)? != completed.evidence {
            return Err(SummaryBlocker::WrongContext);
        }
        let DefinitionRef::Template(_) = completed.evidence.context().definition() else {
            return Err(SummaryBlocker::WrongContext);
        };
        let mut outputs = Vec::new();
        for output in &instance.outputs {
            outputs.extend(self.checked_output_read_sites(facts, output.applied_port())?);
        }
        Ok((
            CompletedChild {
                caller: caller.clone(),
                site: instance.site,
                indices: instance.indices.clone(),
                completed,
                outputs,
            },
            ready,
        ))
    }

    fn checked_output_read_sites(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
    ) -> Result<Vec<ValidatedComponentOutputRead>, SummaryBlocker> {
        let mut reads = Vec::new();
        for id in facts.cfg().nodes() {
            let Some(CfgNodeKind::Evaluate(expression)) = facts.cfg().node(*id).map(|n| &n.kind)
            else {
                continue;
            };
            let Some(ExprKind::Access(path)) =
                self.hir().expression(*expression).map(|expr| &expr.kind)
            else {
                continue;
            };
            if facts.handle_relation(applied.handle(), path) != InstanceRelation::Exact {
                continue;
            }
            match facts.reachable_node(*id).certified() {
                Some(true) => reads.push(ValidatedComponentOutputRead {
                    site: *id,
                    path: path.clone(),
                    applied: applied.clone(),
                }),
                Some(false) => {}
                None => return Err(SummaryBlocker::ExternalSummary),
            }
        }
        Ok(reads)
    }

    pub(super) fn completed_project_template(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        children: &[CompletedChild],
    ) -> Result<CompletedTemplate, SummaryBlocker> {
        self.check_facts_for_evidence(facts, evidence)?;
        self.validated_definition(facts)?;
        self.check_warning_execution_scope(facts, evidence)?;
        if certified(&facts.reachable_node(facts.cfg().exit()))? != &true {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        let constructors = self.completed_constructor_reads(facts, evidence, children)?;
        certified(&facts.body_signal_reads_ready_with(&constructors))?;
        certified(&facts.generated_constraints_valid())?;
        certified(&facts.no_possible_repeated_body_writes())?;
        Ok(CompletedTemplate { evidence: evidence.clone() })
    }

    pub(super) fn completed_constructor_reads(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        children: &[CompletedChild],
    ) -> Result<ValidatedConstructorReads, SummaryBlocker> {
        let mut calls = BTreeSet::new();
        let mut instances = BTreeSet::new();
        let mut outputs = Vec::new();
        for child in children {
            if &child.caller != evidence || !instances.insert((child.site, child.indices.clone())) {
                return Err(SummaryBlocker::WrongContext);
            }
            let site = self.graph().site(child.site).ok_or(SummaryBlocker::ForeignCall)?;
            if child.completed.evidence.context().definition()
                != site.resolved().ok_or(SummaryBlocker::ForeignCall)?
            {
                return Err(SummaryBlocker::WrongContext);
            }
            calls.insert(site.expression.ok_or(SummaryBlocker::ForeignCall)?);
            outputs.extend(child.outputs.iter().cloned());
        }
        self.check_completed_calls(facts, &calls)?;
        Ok(ValidatedConstructorReads { evidence: evidence.clone(), calls, outputs })
    }

    fn check_completed_calls(
        &self,
        facts: &AnalysisFacts<'_>,
        calls: &BTreeSet<ExprId>,
    ) -> Result<(), SummaryBlocker> {
        for site in self.graph().calls_from(CallOwner::Definition(facts.definition())) {
            let Some(DefinitionRef::Template(_)) = site.resolved() else { continue };
            match self.graph().reachable_call(site.id(), facts) {
                CallReachability::Reachable(_) => {
                    let expression = site.expression.ok_or(SummaryBlocker::ForeignCall)?;
                    if !calls.contains(&expression) {
                        return Err(SummaryBlocker::ExternalSummary);
                    }
                }
                CallReachability::Unreachable => {}
                CallReachability::Unavailable(_) => return Err(SummaryBlocker::ExternalSummary),
            }
        }
        Ok(())
    }

    pub(super) fn check_template_incidence_scope(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.check_template_constraint_scope(facts, evidence)?;
        let constructors = self.validated_constructor_reads(facts, evidence)?;
        certified(&facts.body_signal_reads_ready_with(&constructors))?;
        certified(&facts.generated_constraints_valid())?;
        Ok(())
    }

    fn validated_constructor_reads(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<ValidatedConstructorReads, SummaryBlocker> {
        const MAX_CONSTRUCTORS: usize = 64;
        let mut calls = BTreeSet::new();
        for site in self.graph().calls_from(CallOwner::Definition(facts.definition())) {
            let Some(DefinitionRef::Template(_)) = site.resolved() else { continue };
            let call = match self.graph().reachable_call(site.id(), facts) {
                CallReachability::Reachable(call) => call,
                CallReachability::Unreachable => continue,
                CallReachability::Unavailable(_) => return Err(SummaryBlocker::UnsupportedContext),
            };
            if calls.len() >= MAX_CONSTRUCTORS {
                return Err(SummaryBlocker::ContextBudget);
            }
            let child = self.call_evidence(&call, facts, evidence)?;
            self.check_leaf_constructor(&child)?;
            calls.insert(site.expression.ok_or(SummaryBlocker::ForeignCall)?);
        }
        Ok(ValidatedConstructorReads { evidence: evidence.clone(), calls, outputs: Vec::new() })
    }

    fn check_leaf_constructor(&self, evidence: &ContextEvidence) -> Result<(), SummaryBlocker> {
        let DefinitionRef::Template(id) = evidence.context().definition() else {
            return Err(SummaryBlocker::WrongContext);
        };
        let template = self.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
        for port in &template.ports {
            let port = self.hir().port(*port).ok_or(SummaryBlocker::ForeignDefinition)?;
            if port.direction == Some(PortDirection::Input) {
                return Err(SummaryBlocker::MissingInputBinding);
            }
        }
        let cfg = build_cfg(self.hir(), evidence.context().definition()).map_err(|error| {
            SummaryBlocker::LocalAnalysis(format!("leaf constructor analysis: {error:?}"))
        })?;
        let facts = self.analyze_for_evidence(&cfg, evidence, None).map_err(|error| {
            SummaryBlocker::LocalAnalysis(format!("leaf constructor analysis: {error:?}"))
        })?;
        self.check_warning_execution_scope(&facts, evidence)?;
        self.validated_definition(&facts)?;
        if certified(&facts.reachable_node(facts.cfg().exit()))? != &true {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        certified(&facts.body_signal_reads_ready())?;
        certified(&facts.generated_constraints_valid())?;
        certified(&facts.no_possible_repeated_body_writes())?;
        Ok(())
    }
}
