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
