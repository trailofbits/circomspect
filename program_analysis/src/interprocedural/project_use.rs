//! Output-use proofs scoped to a validated, closed `main` root.

use parser::hir::{AccessStep, ArrayIndex, DefinitionRef, PortSchema};
use parser::new_frontend::PortDirection;

use crate::hir_cfg::Origin;
use crate::hir_facts::{AccessHandle, AnalysisFacts};

use super::component::LocalOutputUse;
use super::summary::certified;
use super::{
    AppliedComponentPort, CallOwner, ContextEvidence, ContextOrigin, ProjectSummaries,
    SummaryBlocker, SummaryFact,
};

/// Project-root observation of one exact output path.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ProjectOutputStatus {
    Read,
    Unused,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum OutputTarget {
    Component(Box<AppliedComponentPort>),
    Exported(Box<AccessHandle>),
}

/// A project-wide output-use result for the bounded direct-main subset.
///
/// Only the provider can construct this after validating main, project
/// completeness, and an exact output path. `Unused` never describes a library
/// root or an exported main port.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectOutputUse {
    main: ContextEvidence,
    target: OutputTarget,
    status: ProjectOutputStatus,
    source_reads: Vec<Origin>,
}

impl ProjectOutputUse {
    #[must_use]
    pub fn status(&self) -> ProjectOutputStatus {
        self.status
    }

    #[must_use]
    pub fn handle(&self) -> &AccessHandle {
        match &self.target {
            OutputTarget::Component(applied) => applied.handle(),
            OutputTarget::Exported(handle) => handle,
        }
    }

    #[must_use]
    pub fn main_evidence(&self) -> &ContextEvidence {
        &self.main
    }

    #[must_use]
    pub fn source_reads(&self) -> &[Origin] {
        &self.source_reads
    }
}

impl ProjectSummaries<'_> {
    /// Prove use or non-use of an exact, no-input direct child of validated main.
    pub fn closed_main_component_output_use(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
    ) -> SummaryFact<ProjectOutputUse> {
        SummaryFact::from_result(self.closed_component_result(facts, applied))
    }

    fn closed_component_result(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
    ) -> Result<ProjectOutputUse, SummaryBlocker> {
        let main = applied.caller_evidence();
        self.check_main_root(facts, main)?;
        let DefinitionRef::Template(child) = applied.callee_evidence().context().definition()
        else {
            return Err(SummaryBlocker::WrongInstance);
        };
        let template = self.hir().template(child).ok_or(SummaryBlocker::ForeignDefinition)?;
        for id in &template.ports {
            let port = self.hir().port(*id).ok_or(SummaryBlocker::ForeignDefinition)?;
            if port.direction == Some(PortDirection::Input) {
                return Err(SummaryBlocker::UnsupportedContext);
            }
        }
        let use_state = self.local_output_use_result(facts, applied)?;
        let use_state = match use_state {
            LocalOutputUse::Read(sites) => LocalOutputUse::Read(sites),
            LocalOutputUse::NoLocalRead => self.child_output_use(child, applied)?,
        };
        let (status, source_reads) = match use_state {
            LocalOutputUse::Read(sites) => (ProjectOutputStatus::Read, sites),
            LocalOutputUse::NoLocalRead => (ProjectOutputStatus::Unused, Vec::new()),
        };
        Ok(ProjectOutputUse {
            main: main.clone(),
            target: OutputTarget::Component(Box::new(applied.clone())),
            status,
            source_reads,
        })
    }

    fn child_output_use(
        &self,
        child: parser::hir::TemplateId,
        applied: &AppliedComponentPort,
    ) -> Result<LocalOutputUse, SummaryBlocker> {
        let port = applied.port_summary().port();
        let indices = applied.port_summary().indices();
        self.with_local_template(child, applied.callee_evidence().context(), |_, _, facts| {
            let handle = facts
                .port_handle(port, indices)
                .map_err(|error| SummaryBlocker::LocalAnalysis(error.to_string()))?;
            self.local_handle_use_result(facts, &handle)
        })
    }

    /// Treat a declared output of the validated main template as environment-read.
    pub fn exported_main_output_use(
        &self,
        facts: &AnalysisFacts<'_>,
        main: &ContextEvidence,
        handle: &AccessHandle,
    ) -> SummaryFact<ProjectOutputUse> {
        SummaryFact::from_result(self.exported_output_result(facts, main, handle))
    }

    fn exported_output_result(
        &self,
        facts: &AnalysisFacts<'_>,
        main: &ContextEvidence,
        handle: &AccessHandle,
    ) -> Result<ProjectOutputUse, SummaryBlocker> {
        self.check_main_root(facts, main)?;
        if handle.component().is_some() {
            return Err(SummaryBlocker::WrongInstance);
        }
        let DefinitionRef::Template(id) = facts.definition() else {
            return Err(SummaryBlocker::WrongContext);
        };
        let indices = Self::local_indices(handle)?;
        let template = self.hir().template(id).ok_or(SummaryBlocker::ForeignDefinition)?;
        let mut exported = false;
        for id in &template.ports {
            let port = self.hir().port(*id).ok_or(SummaryBlocker::ForeignDefinition)?;
            let checked_schema = match port.schema {
                PortSchema::Opaque(_) => false,
                PortSchema::Signal | PortSchema::Bus(_) => true,
            };
            if port.direction != Some(PortDirection::Output) || !checked_schema {
                continue;
            }
            if facts.port_handle(*id, &indices).ok().as_ref() == Some(handle) {
                exported = true;
                break;
            }
        }
        if !exported {
            return Err(SummaryBlocker::WrongInstance);
        }
        Ok(ProjectOutputUse {
            main: main.clone(),
            target: OutputTarget::Exported(Box::new(handle.clone())),
            status: ProjectOutputStatus::Read,
            source_reads: Vec::new(),
        })
    }

    fn local_indices(handle: &AccessHandle) -> Result<Vec<usize>, SummaryBlocker> {
        let mut indices = Vec::new();
        for step in &handle.path().steps {
            let AccessStep::Index { index: ArrayIndex::Constant(value), .. } = step else {
                return Err(SummaryBlocker::WrongInstance);
            };
            indices.push(value.parse().map_err(|_| SummaryBlocker::WrongInstance)?);
        }
        Ok(indices)
    }

    fn check_main_root(
        &self,
        facts: &AnalysisFacts<'_>,
        main: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.check_facts_for_evidence(facts, main)?;
        if !self.source_complete() || self.hir().mains().len() != 1 {
            return Err(SummaryBlocker::ExternalSummary);
        }
        let ContextOrigin::Main(id) = main.origin() else {
            return Err(SummaryBlocker::UnsupportedContext);
        };
        let site = self.graph().site(id).ok_or(SummaryBlocker::ForeignCall)?;
        if site.owner != CallOwner::Main(0) || site.resolved() != Some(facts.definition()) {
            return Err(SummaryBlocker::WrongContext);
        }
        if !*certified(&facts.reachable_node(facts.cfg().exit()))? {
            return Err(SummaryBlocker::ExternalSummary);
        }
        Ok(())
    }
}
