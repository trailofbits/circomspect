use crate::hir::{HirProject, Knownness, ValueEvidence};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct SymbolState {
    pub(super) knownness: Knownness,
    pub(super) value_evidence: ValueEvidence,
}

/// Evidence for a stable prefix of the symbol arena; later declarations are outside this snapshot.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SymbolSnapshot {
    states: Vec<SymbolState>,
}

impl SymbolSnapshot {
    pub(super) fn capture(hir: &HirProject) -> Self {
        let mut states = Vec::with_capacity(hir.symbols.len());
        for symbol in &hir.symbols {
            states.push(SymbolState {
                knownness: symbol.knownness,
                value_evidence: symbol.value_evidence,
            });
        }
        Self { states }
    }

    pub(super) fn get(&self, index: usize) -> Option<&SymbolState> {
        self.states.get(index)
    }

    /// Joins only the common prefix, leaving branch-local arena suffixes outside the result.
    pub(super) fn join(&self, other: &Self) -> Self {
        let mut states = Vec::with_capacity(self.states.len().min(other.states.len()));
        for (left, right) in self.states.iter().zip(&other.states) {
            states.push(SymbolState {
                knownness: left.knownness.join(right.knownness),
                value_evidence: left.value_evidence.join(right.value_evidence),
            });
        }
        Self { states }
    }

    pub(super) fn install(&self, hir: &mut HirProject) {
        for (symbol, state) in hir.symbols.iter_mut().zip(&self.states) {
            symbol.knownness = state.knownness;
            symbol.value_evidence = state.value_evidence;
        }
    }
}

#[cfg(test)]
mod tests;
