use std::collections::{btree_map::Entry, BTreeMap};
use std::sync::{Mutex, MutexGuard, PoisonError};

use parser::hir::PortId;

use crate::interprocedural::{
    CallContext, FunctionEffects, FunctionSummary, PortSummary, SummaryFact, WitnessSite,
};

// The limit bounds retained memory only. A full cache recomputes a query without changing facts.
const MAX_CACHE_ENTRIES: usize = 256;

pub(super) struct CertifiedCache<K, V> {
    values: Mutex<BTreeMap<K, V>>,
}

impl<K, V> Default for CertifiedCache<K, V> {
    fn default() -> Self {
        Self { values: Mutex::new(BTreeMap::new()) }
    }
}

impl<K: Ord, V: Clone> CertifiedCache<K, V> {
    fn values(&self) -> MutexGuard<'_, BTreeMap<K, V>> {
        // A poisoned lock cannot corrupt evidence: only completed certified values are inserted.
        self.values.lock().unwrap_or_else(PoisonError::into_inner)
    }

    pub(super) fn get_or_compute(
        &self,
        key: K,
        compute: impl FnOnce() -> SummaryFact<V>,
    ) -> SummaryFact<V> {
        if let Some(value) = self.values().get(&key) {
            return SummaryFact::known(value.clone());
        }
        let fact = compute();
        let Some(value) = fact.certified() else { return fact };
        let mut values = self.values();
        if values.len() >= MAX_CACHE_ENTRIES {
            return fact;
        }
        match values.entry(key) {
            Entry::Vacant(entry) => {
                entry.insert(value.clone());
                fact
            }
            Entry::Occupied(entry) => SummaryFact::known(entry.get().clone()),
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(super) struct PortKey {
    context: CallContext,
    port: PortId,
    indices: Vec<usize>,
}

impl PortKey {
    pub(super) fn new(context: &CallContext, port: PortId, indices: &[usize]) -> Self {
        Self { context: context.clone(), port, indices: indices.to_vec() }
    }
}

#[derive(Default)]
pub(super) struct SummaryCaches {
    pub(super) returns: CertifiedCache<CallContext, FunctionSummary>,
    pub(super) effects: CertifiedCache<CallContext, FunctionEffects>,
    pub(super) ports: CertifiedCache<PortKey, PortSummary>,
    pub(super) reads: CertifiedCache<PortKey, bool>,
    pub(super) witnesses: CertifiedCache<PortKey, Vec<WitnessSite>>,
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;

    use crate::interprocedural::cache::{CertifiedCache, MAX_CACHE_ENTRIES};
    use crate::interprocedural::{SummaryBlocker, SummaryFact};

    #[test]
    fn repeated_certified_query_uses_its_cached_value() {
        let cache = CertifiedCache::<u8, u8>::default();
        let computations = Cell::new(0);
        let first = cache.get_or_compute(1, || {
            computations.set(computations.get() + 1);
            SummaryFact::from_result(Ok(7))
        });
        let second = cache.get_or_compute(1, || {
            computations.set(computations.get() + 1);
            SummaryFact::from_result(Ok(9))
        });
        assert_eq!(first.certified(), Some(&7));
        assert_eq!(second.certified(), Some(&7));
        assert_eq!(computations.get(), 1);
    }

    #[test]
    fn blocked_query_is_recomputed_and_cannot_poison_another_key() {
        let cache = CertifiedCache::<u8, u8>::default();
        let blocked = cache
            .get_or_compute(1, || SummaryFact::from_result(Err(SummaryBlocker::ContextBudget)));
        let recovered = cache.get_or_compute(1, || SummaryFact::from_result(Ok(3)));
        let other = cache.get_or_compute(2, || SummaryFact::from_result(Ok(4)));
        assert!(blocked.unavailable().is_some());
        assert_eq!(recovered.certified(), Some(&3));
        assert_eq!(other.certified(), Some(&4));
    }

    #[test]
    fn capacity_changes_retention_only() {
        let cache = CertifiedCache::<usize, usize>::default();
        for key in 0..MAX_CACHE_ENTRIES {
            assert_eq!(
                cache.get_or_compute(key, || SummaryFact::from_result(Ok(key))).certified(),
                Some(&key)
            );
        }
        let outside = cache
            .get_or_compute(MAX_CACHE_ENTRIES, || SummaryFact::from_result(Ok(MAX_CACHE_ENTRIES)));
        assert_eq!(outside.certified(), Some(&MAX_CACHE_ENTRIES));
        assert_eq!(
            cache.get_or_compute(0, || SummaryFact::from_result(Ok(99))).certified(),
            Some(&0)
        );
        assert_eq!(
            cache
                .get_or_compute(MAX_CACHE_ENTRIES, || SummaryFact::from_result(Ok(99)))
                .certified(),
            Some(&99)
        );
    }
}
