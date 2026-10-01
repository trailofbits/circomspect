use parser::hir::DefinitionRef;
use parser::new_frontend::Span;

use crate::hir_facts::FactBlocker;
use crate::interprocedural::CallContext;

use super::{Finding, RuleKind};

/// Why a rule cannot decide one source scope from certified evidence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AbstentionReason {
    Fact(FactBlocker),
    SummaryUnavailable(DefinitionRef),
    SymbolicParameters,
    IncompleteDefinition,
    UnsupportedConstruct,
}

/// An unresolved predicate at a specific source location and definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScopedAbstention {
    pub kind: RuleKind,
    pub context: CallContext,
    pub span: Span,
    pub reason: AbstentionReason,
}

impl ScopedAbstention {
    #[must_use]
    pub fn definition(&self) -> DefinitionRef {
        self.context.definition()
    }
}

/// A rule's findings and unresolved scopes remain separate until rendering.
#[derive(Clone, Default)]
pub struct RuleResult {
    findings: Vec<Finding>,
    abstentions: Vec<ScopedAbstention>,
}

impl RuleResult {
    #[must_use]
    pub fn findings(&self) -> &[Finding] {
        &self.findings
    }

    #[must_use]
    pub fn abstentions(&self) -> &[ScopedAbstention] {
        &self.abstentions
    }

    pub fn add_finding(&mut self, finding: Finding) {
        self.findings.push(finding);
    }

    pub fn add_abstention(&mut self, abstention: ScopedAbstention) {
        self.abstentions.push(abstention);
    }

    pub(super) fn append(&mut self, other: Self) {
        self.findings.extend(other.findings);
        self.abstentions.extend(other.abstentions);
    }

    pub(super) fn sort(&mut self) {
        self.findings.sort_by(|left, right| {
            (
                left.kind(),
                left.context(),
                left.primary().source(),
                left.primary().start(),
                left.primary().end(),
                left.message(),
            )
                .cmp(&(
                    right.kind(),
                    right.context(),
                    right.primary().source(),
                    right.primary().start(),
                    right.primary().end(),
                    right.message(),
                ))
        });
        self.abstentions.sort_by(|left, right| {
            (
                left.kind,
                &left.context,
                left.span.source(),
                left.span.start(),
                left.span.end(),
                &left.reason,
            )
                .cmp(&(
                    right.kind,
                    &right.context,
                    right.span.source(),
                    right.span.start(),
                    right.span.end(),
                    &right.reason,
                ))
        });
    }
}
