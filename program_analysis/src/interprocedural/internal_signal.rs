//! Constraint incidence for exact internal signals in a validated root template scope.

use parser::hir::{AccessPath, DefinitionRef, SymbolKind};

use crate::hir_facts::{AnalysisFacts, Incidence};
use crate::interprocedural::{
    ContextEvidence, ContextOrigin, TemplateQueries, SummaryBlocker, SummaryFact,
};
use crate::interprocedural::summary::certified;

impl TemplateQueries<'_, '_> {
    /// Prove generated-constraint incidence for one exact internal signal source path.
    ///
    /// Facts must belong to this provider-issued scope. Failed execution, custom templates,
    /// exported ports, unknown control, and incomplete solving withhold the certificate.
    /// Local reads require initialization and supported generated-constraint source form.
    /// Constructors require validated leaf children without unbound inputs. Called
    /// contexts abstain until their incoming constraint closure can be checked.
    pub fn template_internal_signal_incidence(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        path: &AccessPath,
    ) -> SummaryFact<Incidence> {
        SummaryFact::from_result(self.internal_signal_incidence(facts, evidence, path))
    }

    fn internal_signal_incidence(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
        path: &AccessPath,
    ) -> Result<Incidence, SummaryBlocker> {
        self.analysis.execution().check_template_incidence_scope(facts, evidence)?;
        self.check_internal_signal(path)?;
        certified(&facts.exact_access_key(path))?;
        Ok(*certified(&facts.incidence(path))?)
    }

    fn check_internal_signal(&self, path: &AccessPath) -> Result<(), SummaryBlocker> {
        let symbol =
            self.analysis.hir().symbol(path.root).ok_or(SummaryBlocker::ForeignDefinition)?;
        if symbol.kind != SymbolKind::Signal || path.terminal != path.root {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        if self
            .analysis
            .hir()
            .ports()
            .iter()
            .any(|port| port.symbol == path.root && port.direction.is_some())
        {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        Ok(())
    }

    pub(crate) fn check_template_constraint_scope(
        &self,
        facts: &AnalysisFacts<'_>,
        evidence: &ContextEvidence,
    ) -> Result<(), SummaryBlocker> {
        self.analysis.contexts().check_facts_for_evidence(facts, evidence)?;
        let DefinitionRef::Template(_) = facts.definition() else {
            return Err(SummaryBlocker::WrongContext);
        };
        self.analysis.execution().check_warning_execution_scope(facts, evidence)?;
        self.analysis.sources().validated_definition(facts)?;
        match evidence.origin() {
            ContextOrigin::SymbolicRoot | ContextOrigin::Main(_) => {}
            ContextOrigin::Call(_) => return Err(SummaryBlocker::ExternalSummary),
        }
        if certified(&facts.reachable_node(facts.cfg().exit()))? != &true {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        Ok(())
    }
}
