//! Resolved interprocedural calls and certified summaries.

mod graph;
mod summary;
mod effects;
mod template;
mod context;

pub use context::{
    ArgumentShape, ArgumentValue, CallContext, ContextEvidence, ContextOrigin, ProjectSummaries,
    SummaryBlocker,
};

pub use graph::{
    build_call_graph, CallBlocker, CallGraph, CallGraphError, CallOwner, CallProvenance,
    CallReachability, CallSite, CallSiteId, ReachableCall,
};
pub use summary::{FunctionSummary, SummaryFact};
pub use effects::{FunctionEffect, FunctionEffects};
pub use template::PortSummary;
