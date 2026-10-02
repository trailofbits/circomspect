//! Exact local bit decompositions established by generated equations.

use std::collections::BTreeSet;

use abstract_interpretation::solver::SolveResult;
use parser::hir::{AccessPath, ProjectIdentity, SymbolKind};
use program_structure::utils::constants::Curve;

use crate::hir_cfg::Origin;
use crate::hir_facts::relations::polynomial::{boolean_equation, reconstruction_equation};
use crate::hir_facts::relations::MustEquations;
use crate::hir_facts::{AccessHandle, AccessKey, AnalysisFacts, Fact, FactBlocker};
use crate::interprocedural::ContextEvidence;

const MAX_PROVED_BITS: usize = 512;

/// Generated local equations for an exact input and ordered Boolean bits.
///
/// This certificate establishes a body relation, not the caller's accepted
/// input domain or that two representations survive additional constraints.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BitDecomposition {
    project: ProjectIdentity,
    curve: Curve,
    evidence: ContextEvidence,
    input: AccessKey,
    bits: Vec<AccessKey>,
    boolean_origins: Vec<Vec<Origin>>,
    reconstruction_origins: Vec<Origin>,
}

struct EquationOrigins {
    boolean: Vec<Vec<Origin>>,
    reconstruction: Vec<Origin>,
}

impl BitDecomposition {
    #[must_use]
    pub fn curve(&self) -> &Curve {
        &self.curve
    }

    #[must_use]
    pub fn context(&self) -> &ContextEvidence {
        &self.evidence
    }

    #[must_use]
    pub fn input(&self) -> &AccessKey {
        &self.input
    }

    #[must_use]
    pub fn bits(&self) -> &[AccessKey] {
        &self.bits
    }

    #[must_use]
    pub fn boolean_origins(&self) -> &[Vec<Origin>] {
        &self.boolean_origins
    }

    #[must_use]
    pub fn reconstruction_origins(&self) -> &[Origin] {
        &self.reconstruction_origins
    }
}

impl AnalysisFacts<'_> {
    /// Prove the exact local Boolean and weighted reconstruction equations.
    ///
    /// Bits are ordered from least to most significant. Unknown paths, source
    /// writes, constraints, control, or solver state withhold the certificate.
    pub fn bit_decomposition(
        &self,
        input: &AccessPath,
        bits: &[AccessPath],
    ) -> Fact<Option<BitDecomposition>> {
        if bits.is_empty() || bits.len() > MAX_PROVED_BITS {
            return Fact::blocked(BTreeSet::from([FactBlocker::Budget(self.cfg.exit())]));
        }
        let Some(evidence) = &self.evidence_binding else {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        let input = match self.local_signal_key(input) {
            Ok(key) => key,
            Err(blockers) => return Fact::blocked(blockers),
        };
        let bits = match self.local_bit_keys(bits) {
            Ok(keys) => keys,
            Err(blockers) => return Fact::blocked(blockers),
        };
        self.certify_bit_decomposition(evidence, input, bits)
    }

    /// Prove a local decomposition using context-bound, schema-checked ports.
    ///
    /// Handles can name exact array elements even when source uses an induction
    /// variable. Every handle must belong to this definition and context.
    pub fn bit_decomposition_handles(
        &self,
        input: &AccessHandle,
        bits: &[AccessHandle],
    ) -> Fact<Option<BitDecomposition>> {
        if bits.is_empty() || bits.len() > MAX_PROVED_BITS {
            return Fact::blocked(BTreeSet::from([FactBlocker::Budget(self.cfg.exit())]));
        }
        let Some(evidence) = &self.evidence_binding else {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        let input = match self.local_signal_handle_key(input) {
            Ok(key) => key,
            Err(blockers) => return Fact::blocked(blockers),
        };
        let mut keys = Vec::with_capacity(bits.len());
        for bit in bits {
            match self.local_signal_handle_key(bit) {
                Ok(key) => keys.push(key),
                Err(blockers) => return Fact::blocked(blockers),
            }
        }
        self.certify_bit_decomposition(evidence, input, keys)
    }

    fn certify_bit_decomposition(
        &self,
        evidence: &ContextEvidence,
        input: AccessKey,
        bits: Vec<AccessKey>,
    ) -> Fact<Option<BitDecomposition>> {
        let mut unique = BTreeSet::new();
        for bit in &bits {
            if bit == &input || !unique.insert(bit) {
                return Fact::known(None);
            }
        }
        let equations = match self.complete_local_equations(&input, &bits) {
            Ok(equations) => equations,
            Err(blockers) => return Fact::blocked(blockers),
        };
        let Some(origins) = equations else {
            return Fact::known(None);
        };
        Fact::known(Some(BitDecomposition {
            project: self.hir.identity(),
            curve: self.field.curve().clone(),
            evidence: evidence.clone(),
            input,
            bits,
            boolean_origins: origins.boolean,
            reconstruction_origins: origins.reconstruction,
        }))
    }

    fn local_signal_key(&self, path: &AccessPath) -> Result<AccessKey, BTreeSet<FactBlocker>> {
        self.check_local_signal(path)?;
        let fact = self.exact_access_key(path);
        fact.certified().cloned().ok_or_else(|| fact.unavailable().cloned().unwrap_or_default())
    }

    fn local_signal_handle_key(
        &self,
        handle: &AccessHandle,
    ) -> Result<AccessKey, BTreeSet<FactBlocker>> {
        self.check_local_signal(handle.path())?;
        let fact = self.exact_handle_key(handle);
        fact.certified().cloned().ok_or_else(|| fact.unavailable().cloned().unwrap_or_default())
    }

    fn check_local_signal(&self, path: &AccessPath) -> Result<(), BTreeSet<FactBlocker>> {
        let Some(symbol) = self.hir.symbol(path.root) else {
            return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        if symbol.kind != SymbolKind::Signal || path.root != path.terminal {
            return Err(BTreeSet::from([FactBlocker::AggregateAccess]));
        }
        Ok(())
    }

    fn local_bit_keys(
        &self,
        paths: &[AccessPath],
    ) -> Result<Vec<AccessKey>, BTreeSet<FactBlocker>> {
        let mut keys = Vec::with_capacity(paths.len());
        for path in paths {
            keys.push(self.local_signal_key(path)?);
        }
        Ok(keys)
    }

    fn complete_local_equations(
        &self,
        input: &AccessKey,
        bits: &[AccessKey],
    ) -> Result<Option<EquationOrigins>, BTreeSet<FactBlocker>> {
        let SolveResult::Complete(facts) = &self.forward else {
            return Err(self.forward_completion_blockers());
        };
        let Some(state) = facts.get(&self.cfg.exit()).and_then(|item| item.output.as_ref()) else {
            return Err(BTreeSet::from([FactBlocker::MissingExit]));
        };
        if state.variables().is_none() {
            return Err(BTreeSet::from([FactBlocker::MissingExit]));
        }
        let readiness = self.body_signal_reads_ready();
        if let Some(blockers) = readiness.unavailable() {
            return Err(blockers.clone());
        }
        let generated = self.generated_constraints_valid();
        if let Some(blockers) = generated.unavailable() {
            return Err(blockers.clone());
        }
        let writes = self.no_possible_repeated_body_writes();
        if let Some(blockers) = writes.unavailable() {
            return Err(blockers.clone());
        }
        self.match_local_equations(state.must_equations(), input, bits)
    }

    fn match_local_equations(
        &self,
        must: &MustEquations,
        input: &AccessKey,
        bits: &[AccessKey],
    ) -> Result<Option<EquationOrigins>, BTreeSet<FactBlocker>> {
        let mut boolean_origins = Vec::with_capacity(bits.len());
        for bit in bits {
            let expected = boolean_equation(self.field, bit);
            let Some(origins) = must.origins(&expected) else { return Ok(None) };
            boolean_origins.push(self.constraint_origins(origins)?);
        }
        let expected = reconstruction_equation(self.field, input, bits);
        let Some(origins) = must.origins(&expected) else { return Ok(None) };
        Ok(Some(EquationOrigins {
            boolean: boolean_origins,
            reconstruction: self.constraint_origins(origins)?,
        }))
    }
}
