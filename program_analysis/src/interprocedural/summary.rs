use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::lattice::Lattice;
use abstract_interpretation::graph::FlowGraph;
use parser::hir::{DefinitionRef, FunctionId};

use crate::hir_cfg::{build_cfg, CfgNodeKind};
use crate::hir_facts::{analyze_with_scalar_parameters, Range};

use super::{ArgumentValue, CallContext, CallOwner, CallReachability, ProjectSummaries, SummaryBlocker};

/// A summary certificate is created only after the relevant CFG and calls are complete.
///
/// ```compile_fail
/// use circomspect_program_analysis::interprocedural::SummaryFact;
/// let forged = SummaryFact::known(1);
/// ```
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SummaryFact<T>(SummaryState<T>);

#[derive(Clone, Debug, Eq, PartialEq)]
enum SummaryState<T> {
    Certified(T),
    Unavailable(BTreeSet<SummaryBlocker>),
}

impl<T> SummaryFact<T> {
    fn known(value: T) -> Self {
        Self(SummaryState::Certified(value))
    }

    fn blocked(blocker: SummaryBlocker) -> Self {
        Self(SummaryState::Unavailable(BTreeSet::from([blocker])))
    }

    #[must_use]
    pub fn certified(&self) -> Option<&T> {
        match &self.0 {
            SummaryState::Certified(value) => Some(value),
            SummaryState::Unavailable(_) => None,
        }
    }

    #[must_use]
    pub fn unavailable(&self) -> Option<&BTreeSet<SummaryBlocker>> {
        match &self.0 {
            SummaryState::Certified(_) => None,
            SummaryState::Unavailable(blockers) => Some(blockers),
        }
    }
}

/// Return evidence for one scalar function context.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunctionSummary {
    returns: Range,
    input_dependencies: BTreeSet<usize>,
}

impl FunctionSummary {
    #[must_use]
    pub fn returns(&self) -> &Range {
        &self.returns
    }

    #[must_use]
    pub fn input_dependencies(&self) -> &BTreeSet<usize> {
        &self.input_dependencies
    }
}

impl ProjectSummaries<'_> {
    /// Summarize a scalar function under a validated context key.
    /// Reachable calls remain unavailable until their effects are composed.
    pub fn function(&self, id: FunctionId, context: &CallContext) -> SummaryFact<FunctionSummary> {
        let Some(function) = self.hir().function(id) else {
            return SummaryFact::blocked(SummaryBlocker::ForeignDefinition);
        };
        if context.definition() != DefinitionRef::Function(id) {
            return SummaryFact::blocked(SummaryBlocker::WrongContext);
        }
        if let Err(blocker) = self.check_context(context) {
            return SummaryFact::blocked(blocker);
        }
        let mut parameters = BTreeMap::new();
        for (symbol, argument) in function.parameters.iter().zip(context.arguments()) {
            match argument {
                ArgumentValue::Scalar(value) => {
                    parameters.insert(*symbol, value.clone());
                }
                ArgumentValue::Symbolic(_) => {}
                ArgumentValue::Array(_) | ArgumentValue::Bus(_) => {
                    return SummaryFact::blocked(SummaryBlocker::UnsupportedContext);
                }
            }
        }
        let cfg = match build_cfg(self.hir(), DefinitionRef::Function(id)) {
            Ok(cfg) => cfg,
            Err(error) => {
                return SummaryFact::blocked(SummaryBlocker::LocalAnalysis(format!("{error:?}")));
            }
        };
        let field = crate::hir_facts::FieldContext::for_curve(self.curve().clone());
        let facts = match analyze_with_scalar_parameters(self.hir(), &cfg, &field, parameters, None)
        {
            Ok(facts) => facts,
            Err(error) => {
                return SummaryFact::blocked(SummaryBlocker::LocalAnalysis(format!("{error:?}")));
            }
        };
        let owner = CallOwner::Definition(DefinitionRef::Function(id));
        for site in self.graph().calls_from(owner) {
            match self.graph().reachable_call(site.id(), &facts) {
                CallReachability::Unreachable => {}
                CallReachability::Reachable(_) | CallReachability::Unavailable(_) => {
                    return SummaryFact::blocked(SummaryBlocker::ExternalSummary);
                }
            }
        }
        let mut returns = Range::Unreachable;
        let mut observed = false;
        let mut dependencies = BTreeSet::new();
        for node in cfg.nodes() {
            let Some(CfgNodeKind::Return(expression)) = cfg.node(*node).map(|item| &item.kind)
            else {
                continue;
            };
            let reachable = facts.reachable_expression(*expression);
            match reachable.certified() {
                Some(false) => continue,
                Some(true) => {}
                None => {
                    return SummaryFact::blocked(SummaryBlocker::LocalFacts(
                        reachable.unavailable().cloned().unwrap_or_default(),
                    ));
                }
            }
            let range = facts.range(*expression);
            let Some(range) = range.certified() else {
                return SummaryFact::blocked(SummaryBlocker::LocalFacts(
                    range.unavailable().cloned().unwrap_or_default(),
                ));
            };
            returns.join_assign(range);
            observed = true;
            let used = facts.dependencies(*expression);
            let Some(used) = used.certified() else {
                return SummaryFact::blocked(SummaryBlocker::LocalFacts(
                    used.unavailable().cloned().unwrap_or_default(),
                ));
            };
            for key in used {
                let Some(index) = function.parameters.iter().position(|symbol| *symbol == key.root)
                else {
                    return SummaryFact::blocked(SummaryBlocker::ExternalSummary);
                };
                dependencies.insert(index);
            }
        }
        if !observed {
            return SummaryFact::blocked(SummaryBlocker::MissingReturn);
        }
        SummaryFact::known(FunctionSummary { returns, input_dependencies: dependencies })
    }
}
