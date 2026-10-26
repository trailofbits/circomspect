//! Resolved interprocedural calls and certified summaries.

mod graph;
mod cache;
mod call_results;
mod summary;
mod effects;
mod template;
mod context;
mod source_validity;
mod component;
mod component_port;
mod component_models;
mod input_relation;
mod project_use;
mod project_output_closure;
mod output_enumeration;
mod execution_scope;
mod shape_validity;
mod internal_signal;
mod constraint_relation;
mod bit_decomposition;
mod constructor_readiness;
mod called_port;
mod comparator_range;
pub use crate::interprocedural::comparator_range::ComparatorRangeViolation;

pub(crate) use crate::interprocedural::constructor_readiness::ValidatedConstructorReads;

pub use context::{
    AnalyzeEvidenceError, ArgumentShape, ArgumentValue, CallContext, CallPathSite, ContextEvidence,
    ContextOrigin, ProjectAnalysis, SummaryBlocker,
};

pub use graph::{
    build_call_graph, CallBlocker, CallGraph, CallGraphError, CallOwner, CallProvenance,
    CallReachability, CallSite, CallSiteId, ReachableCall,
};
pub use summary::{FunctionSummary, ReturnEvidence, SummaryFact};
pub use effects::{FunctionEffect, FunctionEffects};
pub use template::{PortSummary, WitnessProvenance, WitnessSite};
pub use component::{AppliedComponentPort, CallerOutputRead, ComposedConstraintFixedOutput};
pub use project_use::{ProjectInstanceStep, ProjectOutputStatus, ProjectOutputUse};
pub use output_enumeration::EnumeratedComponentOutput;
pub use crate::interprocedural::constraint_relation::GeneratedEquationQueries;

pub(crate) use crate::interprocedural::component_models::ValidatedComponentPorts;
pub use crate::interprocedural::component_models::{
    ComponentBitAmbiguity, ComponentBitAmbiguityOutcome, ComponentModelAssignment,
};

pub use crate::interprocedural::source_validity::{ValidatedDefinition, ValidatedHeader};
