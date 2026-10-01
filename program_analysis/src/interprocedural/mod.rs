//! Resolved interprocedural calls and certified summaries.

mod graph;
mod context;

pub use context::{ArgumentShape, ArgumentValue, CallContext, ProjectSummaries, SummaryBlocker};

pub use graph::{
    build_call_graph, CallBlocker, CallGraph, CallGraphError, CallOwner, CallProvenance,
    CallReachability, CallSite, CallSiteId, ReachableCall,
};
