//! Must-equation evidence bound to provider-issued analysis contexts.

mod ambiguity;
mod assignment;
pub(crate) use crate::hir_facts::relations::assignment::GeneratedInputEquation;
mod complete;
mod completion;
mod decomposition;
mod polynomial;

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{FlowGraph, NodeId};
use abstract_interpretation::lattice::Lattice;
use abstract_interpretation::solver::{CertifiedFacts, SolveResult};
use crate::hir_cfg::{Constraint, CfgNodeKind, Origin};
use crate::hir_facts::forward::ForwardState;
use crate::hir_facts::relations::polynomial::witness_equation;
use crate::hir_facts::{
    AnalysisFacts, BodyWriteStatus, Fact, FactBlocker, VisitAccesses, WitnessWriteIssue,
};
use crate::interprocedural::{ContextEvidence, ValidatedComponentPorts};

pub use crate::hir_facts::relations::ambiguity::{
    BitAmbiguity, BitAmbiguityOutcome, BitRepresentation, NoBitAmbiguityCertificate,
};
pub use crate::hir_facts::relations::decomposition::BitDecomposition;
pub(crate) use crate::hir_facts::relations::completion::GeneratedAssignments;
pub(crate) use crate::hir_facts::relations::complete::{GeneratedEquationSites, ProofBudget};
pub(crate) use crate::hir_facts::relations::ambiguity::{generated_models_satisfy, generated_seeds};
pub use crate::hir_facts::relations::polynomial::{NormalizedEquation, QuadraticPolynomial};
pub(crate) use crate::hir_facts::relations::polynomial::{
    constraint_equation, variable_polynomial, ExpressionPolynomial, MustSymbolicVariables,
    NormalizationInputs,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MustEquations {
    Unreachable,
    Reached {
        equations: BTreeMap<NormalizedEquation, BTreeSet<NodeId>>,
        blockers: BTreeSet<NodeId>,
    },
}

impl MustEquations {
    pub(crate) fn reachable_empty() -> Self {
        Self::Reached { equations: BTreeMap::new(), blockers: BTreeSet::new() }
    }

    pub(crate) fn insert(&mut self, equation: NormalizedEquation, origin: NodeId) {
        if let Self::Reached { equations, .. } = self {
            equations.insert(equation, BTreeSet::from([origin]));
        }
    }

    pub(crate) fn block(&mut self, origin: NodeId) {
        if let Self::Reached { blockers, .. } = self {
            blockers.insert(origin);
        }
    }

    pub(crate) fn origins(&self, equation: &NormalizedEquation) -> Option<&BTreeSet<NodeId>> {
        let Self::Reached { equations, .. } = self else { return None };
        equations.get(equation)
    }

    fn equation_at_origin(&self, site: NodeId) -> Option<&NormalizedEquation> {
        let Self::Reached { equations, .. } = self else { return None };
        let mut found = None;
        for (equation, origins) in equations {
            if origins.contains(&site) && found.replace(equation).is_some() {
                return None;
            }
        }
        found
    }

    fn blockers(&self) -> BTreeSet<FactBlocker> {
        let Self::Reached { blockers, .. } = self else { return BTreeSet::new() };
        blockers.iter().map(|site| FactBlocker::UnsupportedRelation(*site)).collect()
    }
}

impl Lattice for MustEquations {
    fn bottom() -> Self {
        Self::Unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unreachable, _) => true,
            (Self::Reached { .. }, Self::Unreachable) => false,
            (
                Self::Reached { equations: left, blockers: left_blockers },
                Self::Reached { equations: right, blockers: right_blockers },
            ) => {
                right.iter().all(|(equation, origins)| {
                    left.get(equation).is_some_and(|known| known.is_subset(origins))
                }) && left_blockers.is_subset(right_blockers)
            }
        }
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        if let Self::Unreachable = other {
            return false;
        }
        if let Self::Unreachable = self {
            *self = other.clone();
            return true;
        }
        let old = self.clone();
        let (
            Self::Reached { equations: left, blockers: left_blockers },
            Self::Reached { equations: right, blockers: right_blockers },
        ) = (&mut *self, other)
        else {
            return false;
        };
        left.retain(|equation, origins| {
            let Some(other_origins) = right.get(equation) else { return false };
            origins.extend(other_origins);
            true
        });
        left_blockers.extend(right_blockers.iter().copied());
        *self != old
    }
}

/// A provider-bound proof that a generated equation matches one unavoidable witness write.
/// Constraint sites collectively establish the equation on every reachable exit path.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GeneratedEquation {
    evidence: ContextEvidence,
    equation: NormalizedEquation,
    witness_origin: Origin,
    constraint_origins: Vec<Origin>,
}

impl GeneratedEquation {
    #[must_use]
    pub fn equation(&self) -> &NormalizedEquation {
        &self.equation
    }

    #[must_use]
    pub const fn witness_origin(&self) -> Origin {
        self.witness_origin
    }

    #[must_use]
    pub fn constraint_origins(&self) -> &[Origin] {
        &self.constraint_origins
    }

    #[must_use]
    pub fn context(&self) -> &ContextEvidence {
        &self.evidence
    }
}

impl AnalysisFacts<'_> {
    /// Certify an identical generated equation for an exact witness write.
    /// Incomplete forward results never release provisional equations.
    pub fn must_equation_for_witness(&self, witness: NodeId) -> Fact<Option<GeneratedEquation>> {
        let Some(node) = self.cfg.node(witness) else {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        let CfgNodeKind::Witness { target, value } = &node.kind else {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        let Some(evidence) = &self.evidence_binding else {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        let SolveResult::Complete(facts) = &self.forward else {
            return Fact::blocked(self.forward_completion_blockers());
        };
        let Some(state) = facts.get(&witness).and_then(|item| item.input.as_ref()) else {
            return Fact::known(None);
        };
        let must_execute = self.must_execute(witness);
        match must_execute.certified() {
            Some(true) => {}
            Some(false) => return Fact::known(None),
            None => return Fact::blocked(must_execute.unavailable().cloned().unwrap_or_default()),
        }
        let readiness = self.body_signal_reads_ready();
        if let Some(blockers) = readiness.unavailable() {
            return Fact::blocked(blockers.clone());
        }
        let mut blockers = self.relation_access_blockers(target, witness);
        blockers.extend(self.relation_access_blockers(value, witness));
        if !blockers.is_empty() {
            return Fact::blocked(blockers);
        }
        let write_status = self.body_write_status(target);
        match write_status.certified() {
            Some(BodyWriteStatus::NoRepeat(_)) => {}
            Some(BodyWriteStatus::DefinitelyRepeated(_)) => {
                return Fact::blocked(BTreeSet::from([FactBlocker::WitnessWrite(
                    witness,
                    WitnessWriteIssue::DefiniteRepeat,
                )]));
            }
            None => {
                return Fact::blocked(write_status.unavailable().cloned().unwrap_or_default());
            }
        }
        let Some(values) = state.variables() else { return Fact::known(None) };
        let Some(symbolic) = state.symbolic() else { return Fact::known(None) };
        let inputs =
            NormalizationInputs::new(self.hir, self.field, values, self.calls.as_deref(), symbolic);
        let Ok(equation) = witness_equation(&inputs, target, *value) else {
            return Fact::blocked(BTreeSet::from([FactBlocker::OpaqueExpression(*value)]));
        };
        let Some(exit) = facts.get(&self.cfg.exit()).and_then(|item| item.output.as_ref()) else {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        };
        let generated = self.generated_constraints_valid();
        if let Some(blockers) = generated.unavailable() {
            return Fact::blocked(blockers.clone());
        }
        let Some(origins) = exit.must_equations().origins(&equation) else {
            return Fact::known(None);
        };
        self.equation_certificate(evidence, node.origin, equation, origins)
    }

    /// Check source form and exact operands of every reachable generated constraint.
    /// This establishes neither witness readiness nor satisfiability.
    pub(crate) fn generated_constraints_valid(&self) -> Fact<()> {
        self.generated_constraints_valid_for(None)
    }

    pub(crate) fn generated_constraints_valid_with(
        &self,
        ports: &ValidatedComponentPorts,
    ) -> Fact<()> {
        if self.evidence_binding.as_ref() != Some(ports.evidence()) {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        }
        self.generated_constraints_valid_for(Some(ports))
    }

    fn generated_constraints_valid_for(&self, ports: Option<&ValidatedComponentPorts>) -> Fact<()> {
        let SolveResult::Complete(facts) = &self.forward else {
            return Fact::blocked(self.forward_completion_blockers());
        };
        let Some(exit) = facts.get(&self.cfg.exit()).and_then(|item| item.output.as_ref()) else {
            return Fact::blocked(BTreeSet::from([FactBlocker::MissingExit]));
        };
        let mut blockers = self.reachable_relation_blockers(facts, ports);
        blockers.extend(exit.must_equations().blockers());
        if blockers.is_empty() {
            Fact::known(())
        } else {
            Fact::blocked(blockers)
        }
    }

    fn equation_certificate(
        &self,
        evidence: &ContextEvidence,
        witness: Option<Origin>,
        equation: NormalizedEquation,
        origins: &BTreeSet<NodeId>,
    ) -> Fact<Option<GeneratedEquation>> {
        let Some(witness_origin) = witness else {
            return Fact::blocked(BTreeSet::from([FactBlocker::ForeignQuery]));
        };
        let constraint_origins = match self.constraint_origins(origins) {
            Ok(origins) => origins,
            Err(blockers) => return Fact::blocked(blockers),
        };
        Fact::known(Some(GeneratedEquation {
            evidence: evidence.clone(),
            equation,
            witness_origin,
            constraint_origins,
        }))
    }

    fn constraint_origins(
        &self,
        origins: &BTreeSet<NodeId>,
    ) -> Result<Vec<Origin>, BTreeSet<FactBlocker>> {
        let mut constraint_origins = Vec::new();
        for origin in origins {
            let Some(node) = self.cfg.node(*origin) else {
                return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
            };
            let blockers = self.relation_constraint_blockers(&node.kind, *origin);
            if !blockers.is_empty() {
                return Err(blockers);
            }
            let Some(source) = node.origin else {
                return Err(BTreeSet::from([FactBlocker::ForeignQuery]));
            };
            constraint_origins.push(source);
        }
        Ok(constraint_origins)
    }

    fn relation_constraint_blockers(
        &self,
        kind: &CfgNodeKind,
        site: NodeId,
    ) -> BTreeSet<FactBlocker> {
        self.relation_constraint_blockers_for(kind, site, None)
    }

    fn relation_constraint_blockers_for(
        &self,
        kind: &CfgNodeKind,
        site: NodeId,
        ports: Option<&ValidatedComponentPorts>,
    ) -> BTreeSet<FactBlocker> {
        let CfgNodeKind::Constraint(constraint) = kind else {
            return BTreeSet::from([FactBlocker::UnsupportedRelation(site)]);
        };
        let mut blockers = BTreeSet::new();
        match constraint {
            Constraint::Assignment { target, value } => {
                blockers.extend(self.relation_access_blockers_for(target, site, ports));
                blockers.extend(self.relation_access_blockers_for(value, site, ports));
            }
            Constraint::Equality { left, right } => {
                blockers.extend(self.relation_access_blockers_for(left, site, ports));
                blockers.extend(self.relation_access_blockers_for(right, site, ports));
            }
        }
        blockers
    }

    fn reachable_relation_blockers(
        &self,
        facts: &CertifiedFacts<NodeId, ForwardState>,
        ports: Option<&ValidatedComponentPorts>,
    ) -> BTreeSet<FactBlocker> {
        let mut blockers = BTreeSet::new();
        for site in self.cfg.nodes() {
            let Some(input) = facts.get(site).and_then(|item| item.input.as_ref()) else {
                continue;
            };
            if input.variables().is_none() {
                continue;
            }
            let Some(node) = self.cfg.node(*site) else { continue };
            if let CfgNodeKind::Constraint(_) = &node.kind {
                blockers.extend(self.relation_constraint_blockers_for(&node.kind, *site, ports));
            }
        }
        blockers
    }

    fn relation_access_blockers(
        &self,
        source: &impl VisitAccesses,
        site: NodeId,
    ) -> BTreeSet<FactBlocker> {
        self.relation_access_blockers_for(source, site, None)
    }

    // Exact scalar parameters are substituted by the same site environment used
    // for normalization; they do not denote generated signal storage.
    fn constant_relation_parameter(&self, path: &parser::hir::AccessPath, site: NodeId) -> bool {
        if path.root != path.terminal
            || !path.steps.is_empty()
            || !self.specialized_parameters.contains(&path.root)
        {
            return false;
        }
        self.site_state(site)
            .and_then(ForwardState::variables)
            .is_some_and(|values| values.contains_key(&path.root))
    }

    fn relation_access_blockers_for(
        &self,
        source: &impl VisitAccesses,
        site: NodeId,
        ports: Option<&ValidatedComponentPorts>,
    ) -> BTreeSet<FactBlocker> {
        let mut blockers = BTreeSet::new();
        let complete = source.visit_accesses_with(
            self.hir,
            &|expression| self.exact_call_value(expression).is_some(),
            &mut |path| {
                if self.constant_relation_parameter(path, site) {
                    return;
                }
                let fact = match ports {
                    Some(ports) => self.exact_closed_component_key(path, site, ports),
                    None => self.exact_access_key_at(path, site),
                };
                if let Some(unavailable) = fact.unavailable() {
                    blockers.extend(unavailable.iter().cloned());
                }
            },
        );
        if !complete {
            blockers.insert(FactBlocker::UnsupportedRelation(site));
        }
        blockers
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use abstract_interpretation::graph::NodeId;
    use abstract_interpretation::lattice::Lattice;
    use program_structure::utils::constants::Curve;

    use crate::hir_facts::field::FieldContext;
    use crate::hir_facts::relations::{MustEquations, NormalizedEquation, QuadraticPolynomial};

    fn equation(field: &FieldContext, number: i32) -> NormalizedEquation {
        NormalizedEquation::between(
            QuadraticPolynomial::constant(field, field.canonical(number.into())),
            QuadraticPolynomial::zero(field),
            field,
        )
    }

    fn states() -> Vec<MustEquations> {
        let field = FieldContext::for_curve(Curve::Bn254);
        let first = equation(&field, 0);
        let second = equation(&field, 1);
        assert_ne!(first, second);
        let mut first_at_one = MustEquations::reachable_empty();
        first_at_one.insert(first.clone(), NodeId::new(1));
        let mut first_at_two = MustEquations::reachable_empty();
        first_at_two.insert(first.clone(), NodeId::new(2));
        let mut second_at_three = MustEquations::reachable_empty();
        second_at_three.insert(second.clone(), NodeId::new(3));
        let mut both = first_at_one.clone();
        both.insert(second, NodeId::new(3));
        let mut first_blocked = first_at_one.clone();
        first_blocked.block(NodeId::new(4));
        let mut second_blocked = first_at_two.clone();
        second_blocked.block(NodeId::new(5));
        vec![
            MustEquations::Unreachable,
            MustEquations::reachable_empty(),
            first_at_one,
            first_at_two,
            second_at_three,
            both,
            first_blocked,
            second_blocked,
        ]
    }

    #[test]
    fn must_equation_lattice_laws_and_transfer_monotonicity() {
        let field = FieldContext::for_curve(Curve::Bn254);
        let added = equation(&field, 1);
        let states = states();
        for left in &states {
            assert!(left.leq(left));
            for right in &states {
                let mut joined = left.clone();
                joined.join_assign(right);
                assert!(left.leq(&joined));
                assert!(right.leq(&joined));
                let mut reverse = right.clone();
                reverse.join_assign(left);
                assert_eq!(joined, reverse);
                if left.leq(right) {
                    let mut left_after = left.clone();
                    let mut right_after = right.clone();
                    left_after.insert(added.clone(), NodeId::new(7));
                    right_after.insert(added.clone(), NodeId::new(7));
                    assert!(left_after.leq(&right_after));
                }
                for upper in &states {
                    if left.leq(upper) && right.leq(upper) {
                        assert!(joined.leq(upper));
                    }
                }
                for third in &states {
                    let mut left_grouped = joined.clone();
                    left_grouped.join_assign(third);
                    let mut right_grouped = right.clone();
                    right_grouped.join_assign(third);
                    let mut right_grouped_join = left.clone();
                    right_grouped_join.join_assign(&right_grouped);
                    assert_eq!(left_grouped, right_grouped_join);
                }
            }
        }
    }

    #[test]
    fn same_equation_at_distinct_sites_survives_join_with_both_origins() {
        let field = FieldContext::for_curve(Curve::Bn254);
        let equation = equation(&field, 1);
        let mut left = MustEquations::reachable_empty();
        left.insert(equation.clone(), NodeId::new(1));
        let mut right = MustEquations::reachable_empty();
        right.insert(equation.clone(), NodeId::new(2));
        left.join_assign(&right);
        assert_eq!(left.origins(&equation).unwrap().len(), 2);
        left.insert(equation.clone(), NodeId::new(3));
        assert_eq!(left.origins(&equation).unwrap(), &BTreeSet::from([NodeId::new(3)]));
        left.join_assign(&MustEquations::reachable_empty());
        assert!(left.origins(&equation).is_none());
    }
}
