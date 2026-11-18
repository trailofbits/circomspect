// Test fixtures intentionally panic on invalid construction.
// Rust 1.74 requires `allow` because `expect` lint attributes are not stable there.
#![allow(clippy::allow_attributes, clippy::unwrap_used)]

use crate::hir::lift::symbol_state::{SymbolSnapshot, SymbolState};
use crate::hir::{HirProject, Knownness, SymbolKind, ValueEvidence};
use crate::frontend::{SourceId, Span};
use proptest::prelude::*;

fn snapshot(values: &[(u8, bool)]) -> SymbolSnapshot {
    let mut states = Vec::new();
    for (knownness, deferred) in values {
        let knownness = [
            Knownness::Constant,
            Knownness::ParameterDependent,
            Knownness::WitnessDependent,
            Knownness::Opaque,
        ][usize::from(*knownness) % 4];
        states.push(SymbolState {
            knownness,
            value_evidence: if *deferred {
                ValueEvidence::Deferred
            } else {
                ValueEvidence::Checked
            },
        });
    }
    SymbolSnapshot { states }
}

proptest! {
    #[test]
    fn snapshot_join_is_a_lattice_over_the_common_prefix(
        a in proptest::collection::vec((any::<u8>(), any::<bool>()), 0..16),
        b in proptest::collection::vec((any::<u8>(), any::<bool>()), 0..16),
        c in proptest::collection::vec((any::<u8>(), any::<bool>()), 0..16),
    ) {
        let a = snapshot(&a);
        let b = snapshot(&b);
        let c = snapshot(&c);
        prop_assert_eq!(a.join(&a), a.clone());
        prop_assert_eq!(a.join(&b), b.join(&a));
        prop_assert_eq!(a.join(&b).join(&c), a.join(&b.join(&c)));
        prop_assert_eq!(a.join(&b).states.len(), a.states.len().min(b.states.len()));
    }
}

#[test]
fn snapshot_install_keeps_newer_arena_symbols_untouched() {
    let mut hir = HirProject::new();
    let span = Span::checked(SourceId::new(0), 0..1, "x").unwrap();
    let first = hir.add_symbol("first".into(), SymbolKind::Variable, span);
    hir.symbols[first.index].knownness = Knownness::Constant;
    let before = SymbolSnapshot::capture(&hir);
    let later = hir.add_symbol("later".into(), SymbolKind::Variable, span);
    hir.symbols[first.index].knownness = Knownness::WitnessDependent;
    hir.symbols[later.index].value_evidence = ValueEvidence::Deferred;
    before.install(&mut hir);
    assert_eq!(hir.symbols[first.index].knownness, Knownness::Constant);
    assert_eq!(hir.symbols[later.index].value_evidence, ValueEvidence::Deferred);
    assert_eq!(hir.symbols.len(), 2);
}
