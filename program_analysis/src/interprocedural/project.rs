//! Project storage shared by borrowed query owners.

use parser::hir::{HirProject, LiftedProject};
use program_structure::utils::constants::Curve;

use crate::hir_facts::FieldContext;
use crate::interprocedural::cache::SummaryCaches;
use crate::interprocedural::source_validity::SourceQueries;
use crate::interprocedural::{build_call_graph, CallGraph, CallGraphError};

/// Owns the validated field and graph used to construct summary contexts.
pub struct ProjectAnalysis<'hir> {
    lifted: &'hir LiftedProject,
    field: FieldContext,
    graph: CallGraph,
    pub(super) caches: SummaryCaches,
}

impl<'hir> ProjectAnalysis<'hir> {
    /// Build a provider for one selected compiler curve and the lifted language version.
    ///
    /// # Errors
    /// Returns a graph error if a call site references an invalid HIR identity.
    pub fn build(lifted: &'hir LiftedProject, curve: Curve) -> Result<Self, CallGraphError> {
        let graph = build_call_graph(&lifted.hir)?;
        Ok(Self {
            lifted,
            field: FieldContext::for_curve(curve),
            graph,
            caches: SummaryCaches::default(),
        })
    }

    #[must_use]
    pub fn hir(&self) -> &HirProject {
        &self.lifted.hir
    }

    pub(super) fn lifted_project(&self) -> &LiftedProject {
        self.lifted
    }

    #[must_use]
    pub fn graph(&self) -> &CallGraph {
        &self.graph
    }

    #[must_use]
    pub fn curve(&self) -> &Curve {
        self.field.curve()
    }

    pub(crate) fn field_context(&self) -> &FieldContext {
        &self.field
    }

    pub(crate) fn sources(&self) -> SourceQueries<'_, 'hir> {
        SourceQueries { analysis: self }
    }
}
