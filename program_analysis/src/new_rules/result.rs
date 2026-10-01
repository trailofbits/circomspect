use parser::hir::DefinitionRef;
use parser::new_frontend::Span;

use crate::hir_facts::FactBlocker;
use crate::interprocedural::CallContext;

use super::Finding;

/// Why a rule cannot decide one source scope from certified evidence.
#[derive(Clone, Debug, Eq, PartialEq)]
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
}
