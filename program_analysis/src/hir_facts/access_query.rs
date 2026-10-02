//! Certified source accesses for consumers that need exact storage identities.

use std::collections::{BTreeMap, BTreeSet};

use parser::hir::{AccessPath, AccessStep, SymbolKind};

use crate::hir_facts::access::key_for_path;
use crate::hir_facts::{
    AccessHandle, AccessKey, AccessKeyStep, AnalysisFacts, Fact, FactBlocker, IndexKey, Range,
};

impl AnalysisFacts<'_> {
    /// Identify one owned scalar storage path with proved dimensions and exact indices.
    ///
    /// Symbolic index syntax is accepted only when its value is certified across every
    /// evaluation site. The key identifies storage; it does not prove reachability,
    /// witness assignment, constraint incidence, or successful execution of the definition.
    pub fn exact_access_key(&self, path: &AccessPath) -> Fact<AccessKey> {
        self.certify_access_key(path, false)
    }

    pub(crate) fn exact_handle_key(&self, handle: &AccessHandle) -> Fact<AccessKey> {
        if handle.definition != self.cfg.definition() {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignDefinition]));
        }
        if handle.curve != *self.field.curve() {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        if let Some(evidence) = &self.evidence_binding {
            if !handle.matches_context(evidence.context()) {
                return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
            }
        }
        self.certify_access_key(handle.path(), true)
    }

    fn certify_access_key(&self, path: &AccessPath, schema_checked: bool) -> Fact<AccessKey> {
        if let Some(blocker) = self.validate_query_path(path, schema_checked) {
            return Fact::blocked(BTreeSet::from([blocker]));
        }
        if !self.scalar_storage_path(path) {
            return Fact::blocked(BTreeSet::from([FactBlocker::AggregateAccess]));
        }
        let key = match self.resolve_access_indices(path) {
            Ok(key) => key,
            Err(blockers) => return Fact::blocked(blockers),
        };
        if self.checked_access_bounds(path).is_err() {
            return Fact::blocked(BTreeSet::from([FactBlocker::AggregateAccess]));
        }
        Fact::known(key)
    }

    fn resolve_access_indices(
        &self,
        path: &AccessPath,
    ) -> Result<AccessKey, BTreeSet<FactBlocker>> {
        let mut key = key_for_path(self.hir, self.field, path, &BTreeMap::new());
        for step in &mut key.steps {
            match step {
                AccessKeyStep::Index(IndexKey::Symbolic(expression)) => {
                    let fact = self.range(*expression);
                    let Some(Range::Exact(value)) = fact.certified() else {
                        return Err(fact.unavailable().cloned().unwrap_or_else(|| {
                            BTreeSet::from([FactBlocker::OpaqueExpression(*expression)])
                        }));
                    };
                    *step = AccessKeyStep::Index(IndexKey::Exact(value.clone()));
                }
                AccessKeyStep::Index(IndexKey::Unknown) => {
                    return Err(BTreeSet::from([FactBlocker::AggregateAccess]));
                }
                AccessKeyStep::Index(IndexKey::Exact(_))
                | AccessKeyStep::Port(_)
                | AccessKeyStep::Tag(_) => {}
            }
        }
        Ok(key)
    }

    fn scalar_storage_path(&self, path: &AccessPath) -> bool {
        let Some(symbol) = self.hir.symbol(path.terminal) else { return false };
        let storage = match symbol.kind {
            SymbolKind::Variable | SymbolKind::Signal | SymbolKind::Tag => true,
            SymbolKind::Parameter | SymbolKind::Component | SymbolKind::Bus => false,
        };
        if !storage || !symbol.shape_checked || symbol.bus_type.is_some() {
            return false;
        }
        let mut indices = 0;
        for step in path.steps.iter().rev() {
            match step {
                AccessStep::Index { .. } => indices += 1,
                AccessStep::Port { .. } | AccessStep::Tag { .. } => break,
            }
        }
        indices == symbol.rank
    }
}
