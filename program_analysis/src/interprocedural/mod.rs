//! Resolved interprocedural calls and certified summaries.

mod graph;

pub use graph::{build_call_graph, CallGraph, CallGraphError, CallOwner, CallProvenance, CallSite};
