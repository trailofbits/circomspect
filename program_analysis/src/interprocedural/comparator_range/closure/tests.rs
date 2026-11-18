use crate::hir_facts::ProofBudget;
use crate::interprocedural::comparator_range::ComparatorQuery;
use crate::interprocedural::comparator_range::tests::{with_query, SOURCE};

#[test]
fn comparator_callback_returns_owned_violations() {
    with_query(SOURCE, |provider, _, facts, applied| {
        let violations = {
            let query = ComparatorQuery { analysis: provider, facts, applied };
            query
                .with_checked_closure(&mut ProofBudget::default(), |closure, budget| {
                    closure.validate_candidate(budget)
                })
                .unwrap()
                .unwrap()
        };
        assert_eq!(violations.len(), 1);
        assert_eq!(violations[0].applied_port(), applied);
        assert_eq!(violations[0].value().as_bigint().to_string(), "4");
        assert_eq!(violations[0].upper_bound().to_string(), "4");
    });
}
