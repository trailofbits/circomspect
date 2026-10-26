//! Resolved interprocedural calls and certified summaries.
//!
//! [`ProjectAnalysis`] owns one project's field, call graph, and completed summary caches.
//! Queries bind results to source identities and context evidence before composing local facts.
//! Function return coverage, function effects, and template ports have distinct policies;
//! their similarly shaped results do not make their recursion or completion checks interchangeable.
//!
//! | Evidence | Issuer module | Required consumer check |
//! | --- | --- | --- |
//! | [`CallContext`] | `context` | Hypothetical keys do not prove reachability |
//! | [`ContextEvidence`] | `context` | Match exact facts and ancestry |
//! | [`ValidatedHeader`] | `source_validity` | Body coverage is separate |
//! | [`ValidatedDefinition`] | `source_validity` | Coverage does not prove execution |
//! | `CheckedCallContext` | `component::binding` | Select and check the source instance |
//! | [`AppliedComponentPort`] | `component::binding` | Check generation and input readiness |
//! | `CompletedTemplate`, `CompletedChild` | `constructor_readiness` | Match current read sites |
//! | `ReadyWitnessInputs` | `input_relation` | Witness values are not generated equations |
//! | `ReadyGeneratedInputs` | `input_relation::generated` | Validate complete model equations |
//! | [`GeneratedEquationQueries`] | `constraint_relation` | Inspect each query's availability |
//! | `CheckedComparatorClosure` | `comparator_range::closure` | Validate every candidate equation |
//! | [`ComponentBitAmbiguity`] | `component_models` | Inspect both models and their provenance |
//! | [`ProjectOutputUse`] | `project_use` | Require the selected rooted closure policy |
//!
//! The issuer types document their identity, borrowing, and coverage contracts in more detail.
//! Constructors stay in those modules; there is no universal certificate that skips the remaining
//! checks. Bounded candidate rejection proves neither uniqueness nor successful witness execution.

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
