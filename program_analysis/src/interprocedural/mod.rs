//! Resolved interprocedural calls and certified summaries.

mod graph;
mod cache;
mod call_results;
mod summary;
mod effects;
mod template;
mod context;
mod component;
mod input_relation;
mod project_use;
mod output_enumeration;
mod validity;
mod execution_scope;
mod shape_validity;
mod internal_signal;
mod constraint_relation;
mod bit_decomposition;
mod constructor_readiness;

pub(crate) use crate::interprocedural::constructor_readiness::ValidatedConstructorReads;

pub use context::{
    AnalyzeEvidenceError, ArgumentShape, ArgumentValue, CallContext, CallPathSite, ContextEvidence,
    ContextOrigin, ProjectSummaries, SummaryBlocker, ValidatedDefinition, ValidatedHeader,
};

pub use graph::{
    build_call_graph, CallBlocker, CallGraph, CallGraphError, CallOwner, CallProvenance,
    CallReachability, CallSite, CallSiteId, ReachableCall,
};
pub use summary::{FunctionSummary, ReturnEvidence, SummaryFact};
pub use effects::{FunctionEffect, FunctionEffects};
pub use template::{PortSummary, WitnessProvenance, WitnessSite};
pub use component::{AppliedComponentPort, CallerOutputRead, ComposedConstraintFixedOutput};
pub use project_use::{ProjectOutputStatus, ProjectOutputUse};
pub use output_enumeration::EnumeratedComponentOutput;
