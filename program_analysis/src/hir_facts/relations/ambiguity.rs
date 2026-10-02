//! Finite candidate models validated against every generated equation in a root scope.

mod control;

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;
use parser::hir::{AccessPath, AccessStep, SymbolKind};
use parser::new_frontend::PortDirection;

use crate::hir_cfg::Origin;
use crate::hir_facts::relations::complete::{GeneratedEquationSites, ProofBudget};
use crate::hir_facts::{
    AccessKey, AccessKeyStep, AnalysisFacts, BitDecomposition, Fact, FactBlocker, FieldContext,
    FieldValue,
};

/// Outcome of the bounded search for two satisfying bit representations.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BitAmbiguityOutcome {
    Proved(Box<BitAmbiguity>),
    NoCertificate(NoBitAmbiguityCertificate),
}

/// Why the complete finite candidate check did not produce a pair.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NoBitAmbiguityCertificate {
    /// The generated equations do not establish the requested ordered bit relation.
    NoMatchingDecomposition,
    /// The integer encoding range contains no two distinct values congruent modulo p.
    WidthBelowFieldModulus,
    /// The chosen finite pair failed; this does not establish uniqueness or unsatisfiability.
    CandidatesRejected,
}

/// One nonnegative integer encoded by an exact ordered Boolean vector.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BitRepresentation {
    integer: BigUint,
    bits: Vec<bool>,
}

impl BitRepresentation {
    #[must_use]
    pub fn integer(&self) -> &BigUint {
        &self.integer
    }

    #[must_use]
    pub fn bits(&self) -> &[bool] {
        &self.bits
    }

    fn new(integer: BigUint, width: usize) -> Option<Self> {
        if integer >= BigUint::from(1_u8) << width {
            return None;
        }
        let bytes = integer.to_bytes_le();
        let mut bits = Vec::with_capacity(width);
        for index in 0..width {
            let byte = bytes.get(index / 8).copied().unwrap_or(0);
            bits.push(byte & (1 << (index % 8)) != 0);
        }
        Some(Self { integer, bits })
    }
}

/// Two models of every generated equation in one provider-validated leaf scope.
///
/// The same external inputs admit distinct bit vectors. Unmentioned local field
/// signals can be extended with zero because no generated equation uses them.
/// This says neither that the honest witness generator produces these models
/// nor that another caller's constraints permit them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BitAmbiguity {
    decomposition: BitDecomposition,
    input: FieldValue,
    representations: [BitRepresentation; 2],
    assignments: [BTreeMap<AccessKey, FieldValue>; 2],
    constraint_origins: Vec<Origin>,
}

impl BitAmbiguity {
    #[must_use]
    pub fn decomposition(&self) -> &BitDecomposition {
        &self.decomposition
    }

    #[must_use]
    pub fn input_value(&self) -> &FieldValue {
        &self.input
    }

    #[must_use]
    pub fn representations(&self) -> &[BitRepresentation; 2] {
        &self.representations
    }

    #[must_use]
    pub fn assignments(&self) -> &[BTreeMap<AccessKey, FieldValue>; 2] {
        &self.assignments
    }

    #[must_use]
    pub fn constraint_origins(&self) -> &[Origin] {
        &self.constraint_origins
    }
}

struct CandidateModel(BTreeMap<AccessKey, FieldValue>);

struct ValidatedModelPair([CandidateModel; 2]);

impl AnalysisFacts<'_> {
    pub(crate) fn local_bit_ambiguity(
        &self,
        input: &AccessPath,
        bits: &[AccessPath],
        budget: &mut ProofBudget,
    ) -> Fact<BitAmbiguityOutcome> {
        match self.bit_ambiguity_result(input, bits, budget) {
            Ok(result) => Fact::known(result),
            Err(blockers) => Fact::blocked(blockers),
        }
    }

    fn bit_ambiguity_result(
        &self,
        input: &AccessPath,
        bits: &[AccessPath],
        budget: &mut ProofBudget,
    ) -> Result<BitAmbiguityOutcome, BTreeSet<FactBlocker>> {
        self.check_model_paths(input, bits)?;
        let path = self.unique_generation_path(budget)?;
        let relation = self.bit_decomposition(input, bits);
        let Some(relation) = relation.certified() else {
            return Err(relation
                .unavailable()
                .cloned()
                .unwrap_or_else(|| BTreeSet::from([FactBlocker::ForeignQuery])));
        };
        let Some(relation) = relation else {
            return Ok(no_certificate(NoBitAmbiguityCertificate::NoMatchingDecomposition));
        };
        let generated = self.generated_equation_sites(budget);
        let Some(generated) = generated.certified() else {
            return Err(generated
                .unavailable()
                .cloned()
                .unwrap_or_else(|| BTreeSet::from([FactBlocker::ForeignQuery])));
        };
        if generated.evidence() != relation.context() {
            return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        self.check_model_keys(generated.keys())?;
        for site in generated.sites() {
            if !path.contains(&site.site()) {
                return Err(BTreeSet::from([FactBlocker::UnsupportedRelation(site.site())]));
            }
        }
        prove_candidates(self.field, relation, generated, budget)
    }

    fn check_model_keys(&self, keys: &BTreeSet<AccessKey>) -> Result<(), BTreeSet<FactBlocker>> {
        for key in keys {
            let Some(symbol) = self.hir.symbol(key.root) else {
                return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
            };
            if symbol.kind != SymbolKind::Signal || key.instance.is_some() || !key.exact_alias(key)
            {
                return Err(BTreeSet::from([FactBlocker::AggregateAccess]));
            }
            for step in &key.steps {
                match step {
                    AccessKeyStep::Index(_) => {}
                    AccessKeyStep::Port(_) | AccessKeyStep::Tag(_) => {
                        return Err(BTreeSet::from([FactBlocker::AggregateAccess]));
                    }
                }
            }
        }
        Ok(())
    }

    fn check_model_paths(
        &self,
        input: &AccessPath,
        bits: &[AccessPath],
    ) -> Result<(), BTreeSet<FactBlocker>> {
        for path in std::iter::once(input).chain(bits) {
            for step in &path.steps {
                match step {
                    AccessStep::Index { .. } => {}
                    AccessStep::Port { .. } | AccessStep::Tag { .. } => {
                        return Err(BTreeSet::from([FactBlocker::AggregateAccess]));
                    }
                }
            }
        }
        for bit in bits {
            if self
                .hir
                .ports()
                .iter()
                .any(|port| port.symbol == bit.root && port.direction == Some(PortDirection::Input))
            {
                return Err(BTreeSet::from([FactBlocker::AggregateAccess]));
            }
        }
        Ok(())
    }
}

fn no_certificate(reason: NoBitAmbiguityCertificate) -> BitAmbiguityOutcome {
    BitAmbiguityOutcome::NoCertificate(reason)
}

fn prove_candidates(
    field: &FieldContext,
    relation: &BitDecomposition,
    generated: &GeneratedEquationSites<'_>,
    budget: &mut ProofBudget,
) -> Result<BitAmbiguityOutcome, BTreeSet<FactBlocker>> {
    let modulus =
        field.modulus().to_biguint().ok_or_else(|| BTreeSet::from([FactBlocker::ForeignQuery]))?;
    let limit = BigUint::from(1_u8) << relation.bits().len();
    if limit <= modulus {
        return Ok(no_certificate(NoBitAmbiguityCertificate::WidthBelowFieldModulus));
    }
    let Some(seeds) = generated_seeds(field, generated, budget)? else {
        return Ok(no_certificate(NoBitAmbiguityCertificate::CandidatesRejected));
    };
    let input = seeds.get(relation.input()).cloned().unwrap_or_else(|| field.canonical(0.into()));
    let integer = input
        .as_bigint()
        .to_biguint()
        .ok_or_else(|| BTreeSet::from([FactBlocker::ForeignQuery]))?;
    let Some(second) = BitRepresentation::new(&integer + modulus, relation.bits().len()) else {
        return Ok(no_certificate(NoBitAmbiguityCertificate::CandidatesRejected));
    };
    let Some(first) = BitRepresentation::new(integer, relation.bits().len()) else {
        return Ok(no_certificate(NoBitAmbiguityCertificate::CandidatesRejected));
    };
    let representations = [first, second];
    let models = candidate_models(field, relation, generated, &seeds, &representations);
    let Some(ValidatedModelPair([first, second])) =
        validate_models(field, generated, models, budget)?
    else {
        return Ok(no_certificate(NoBitAmbiguityCertificate::CandidatesRejected));
    };
    let mut constraint_origins = Vec::with_capacity(generated.sites().len());
    for site in generated.sites() {
        constraint_origins.push(site.origin());
    }
    Ok(BitAmbiguityOutcome::Proved(Box::new(BitAmbiguity {
        decomposition: relation.clone(),
        input,
        representations,
        assignments: [first.0, second.0],
        constraint_origins,
    })))
}

fn generated_seeds(
    field: &FieldContext,
    generated: &GeneratedEquationSites<'_>,
    budget: &mut ProofBudget,
) -> Result<Option<BTreeMap<AccessKey, FieldValue>>, BTreeSet<FactBlocker>> {
    let mut seeds = BTreeMap::new();
    for site in generated.sites() {
        if !budget.reserve_evaluation(site.equation()) {
            return Err(BTreeSet::from([FactBlocker::Budget(site.site())]));
        }
        let seed = site
            .equation()
            .singleton_solution(field)
            .map_err(|_| BTreeSet::from([FactBlocker::UnsupportedRelation(site.site())]))?;
        if let Some((key, value)) = seed {
            if let Some(previous) = seeds.insert(key, value.clone()) {
                if previous != value {
                    return Ok(None);
                }
            }
        }
    }
    Ok(Some(seeds))
}

fn candidate_models(
    field: &FieldContext,
    relation: &BitDecomposition,
    generated: &GeneratedEquationSites<'_>,
    seeds: &BTreeMap<AccessKey, FieldValue>,
    representations: &[BitRepresentation; 2],
) -> [CandidateModel; 2] {
    [&representations[0], &representations[1]].map(|representation| {
        let mut model = BTreeMap::new();
        for key in generated.keys() {
            model.insert(
                key.clone(),
                seeds.get(key).cloned().unwrap_or_else(|| field.canonical(0.into())),
            );
        }
        for (key, bit) in relation.bits().iter().zip(&representation.bits) {
            model.insert(key.clone(), field.canonical(i32::from(*bit).into()));
        }
        CandidateModel(model)
    })
}

fn validate_models(
    field: &FieldContext,
    generated: &GeneratedEquationSites<'_>,
    models: [CandidateModel; 2],
    budget: &mut ProofBudget,
) -> Result<Option<ValidatedModelPair>, BTreeSet<FactBlocker>> {
    for site in generated.sites() {
        for model in &models {
            if !budget.reserve_evaluation(site.equation()) {
                return Err(BTreeSet::from([FactBlocker::Budget(site.site())]));
            }
            let value = site
                .equation()
                .evaluate(field, &model.0)
                .map_err(|_| BTreeSet::from([FactBlocker::UnsupportedRelation(site.site())]))?;
            if !field.is_zero(&value) {
                return Ok(None);
            }
        }
    }
    Ok(Some(ValidatedModelPair(models)))
}

#[cfg(test)]
mod tests;
