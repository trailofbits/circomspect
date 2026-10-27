//! Two complete constraint models for one checked child of an exact main instance.

mod models;
mod ports;
mod source;

use std::collections::BTreeMap;

use parser::hir::{AccessPath, PortId, PortSchema};
use parser::frontend::PortDirection;

use crate::hir_cfg::Origin;
use crate::hir_facts::{
    RankOnePortError, AccessHandle, AccessKey, AnalysisFacts, BitDecomposition, BitRepresentation,
    FieldValue, NoBitAmbiguityCertificate, ProofBudget,
};
use crate::interprocedural::component_models::models::{prove_closure_models, ClosureEquations};
use crate::interprocedural::summary::certified;
use crate::interprocedural::{AppliedComponentPort, ProjectAnalysis, SummaryBlocker, SummaryFact};

pub(crate) use crate::interprocedural::component_models::ports::ValidatedComponentPorts;

/// Result of the finite two-model search over a complete single-child main closure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ComponentBitAmbiguityOutcome {
    Proved(Box<ComponentBitAmbiguity>),
    NoCertificate(NoBitAmbiguityCertificate),
}

/// Assignments in two separate storage namespaces bound by a checked component call.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ComponentModelAssignment {
    caller: BTreeMap<AccessKey, FieldValue>,
    callee: BTreeMap<AccessKey, FieldValue>,
}

impl ComponentModelAssignment {
    #[must_use]
    pub fn caller(&self) -> &BTreeMap<AccessKey, FieldValue> {
        &self.caller
    }

    #[must_use]
    pub fn callee(&self) -> &BTreeMap<AccessKey, FieldValue> {
        &self.callee
    }
}

/// Two assignments satisfying every generated equation in the exact main and child.
///
/// Parent external inputs and bound child inputs are equal in both assignments.
/// Witness-only values do not restrict these models. This proves existence of two
/// constraint models, not that the witness generator produces either assignment.
/// Maps retain finite equation support; unmentioned signal cells extend with zero.
///
/// The model issuer checks two different bit representations against complete parent/child
/// equations with the same external and bound inputs. Assignments and source origins retain
/// the checked applied-port identity. This proves constraint ambiguity, not witness-generator
/// execution; failure to find such a pair does not prove uniqueness.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ComponentBitAmbiguity {
    applied: AppliedComponentPort,
    decomposition: BitDecomposition,
    input: FieldValue,
    representations: [BitRepresentation; 2],
    assignments: [ComponentModelAssignment; 2],
    caller_origins: Vec<Origin>,
    callee_origins: Vec<Origin>,
    binding_origins: Vec<Origin>,
}

impl ComponentBitAmbiguity {
    #[must_use]
    pub fn applied_port(&self) -> &AppliedComponentPort {
        &self.applied
    }

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
    pub fn assignments(&self) -> &[ComponentModelAssignment; 2] {
        &self.assignments
    }

    #[must_use]
    pub fn caller_constraint_origins(&self) -> &[Origin] {
        &self.caller_origins
    }

    #[must_use]
    pub fn callee_constraint_origins(&self) -> &[Origin] {
        &self.callee_origins
    }

    #[must_use]
    pub fn input_binding_origins(&self) -> &[Origin] {
        &self.binding_origins
    }
}

#[derive(Clone, Copy)]
enum RequestedBits<'a> {
    Paths { input: &'a AccessPath, bits: &'a [AccessPath] },
    Handles { input: &'a AccessHandle, bits: &'a [AccessHandle] },
    Ports { input: PortId, bits: PortId },
}

impl ProjectAnalysis<'_> {
    /// Prove two constraint models for one exact leaf child under an instantiated main.
    ///
    /// `applied` must identify that main's sole child. `input` and the ordered `bits`
    /// belong to that child's exact parameter context. Unknown control, incomplete
    /// input bindings, extra children or exhausted budgets withhold the certificate.
    /// A rejected finite pair does not establish uniqueness or unsatisfiability.
    pub fn component_bit_ambiguity(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
        input: &AccessPath,
        bits: &[AccessPath],
    ) -> SummaryFact<ComponentBitAmbiguityOutcome> {
        SummaryFact::from_result(self.component_ambiguity_result(
            facts,
            applied,
            RequestedBits::Paths { input, bits },
            &mut ProofBudget::default(),
        ))
    }

    /// Prove the same complete closure using checked child-local port handles.
    ///
    /// Every handle must match the selected child's exact context, project, curve
    /// and port schema. This form supports elements named by specialized loop indices.
    pub fn component_bit_ambiguity_handles(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
        input: &AccessHandle,
        bits: &[AccessHandle],
    ) -> SummaryFact<ComponentBitAmbiguityOutcome> {
        SummaryFact::from_result(self.component_ambiguity_result(
            facts,
            applied,
            RequestedBits::Handles { input, bits },
            &mut ProofBudget::default(),
        ))
    }

    /// Prove two complete caller and child models using checked child port schemas.
    ///
    /// The scalar input and rank-one bit output are resolved in the callee's
    /// exact parameter context. The provider creates every element handle and
    /// refuses zero, unproved, or over-budget widths before model validation.
    pub fn component_bit_ambiguity_ports(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
        input: PortId,
        bits: PortId,
    ) -> SummaryFact<ComponentBitAmbiguityOutcome> {
        SummaryFact::from_result(self.component_ambiguity_result(
            facts,
            applied,
            RequestedBits::Ports { input, bits },
            &mut ProofBudget::default(),
        ))
    }

    fn component_ambiguity_result(
        &self,
        facts: &AnalysisFacts<'_>,
        applied: &AppliedComponentPort,
        requested: RequestedBits<'_>,
        budget: &mut ProofBudget,
    ) -> Result<ComponentBitAmbiguityOutcome, SummaryBlocker> {
        if let RequestedBits::Ports { bits, .. } = &requested {
            let (port, indices) =
                applied.handle().output_port().ok_or(SummaryBlocker::WrongInstance)?;
            if port != *bits || indices.as_slice() != [0] {
                return Err(SummaryBlocker::WrongInstance);
            }
        }
        self.check_model_main_root(facts, applied.caller_evidence())?;
        self.sources().validated_definition(facts)?;
        self.execution().check_warning_execution_scope(facts, applied.caller_evidence())?;
        self.check_parent_components_complete(facts)?;
        self.single_model_call(facts, applied)?;
        self.components().with_component_port_facts(applied.callee_evidence(), |child| {
            let instance = self.model_source_instance(facts, child, applied, budget)?;
            let completed =
                self.execution().completed_project_template(child, &instance.callee, &[])?;
            let (completed, ready) = self.execution().completed_model_child(
                facts,
                applied.caller_evidence(),
                &instance,
                completed,
            )?;
            let constructors = self.execution().completed_constructor_reads(
                facts,
                applied.caller_evidence(),
                &[completed],
            )?;
            certified(&facts.body_signal_reads_ready_with(&constructors))?;
            certified(&facts.no_possible_repeated_body_writes())?;
            let relation = match requested {
                RequestedBits::Paths { input, bits } => child.bit_decomposition(input, bits),
                RequestedBits::Handles { input, bits } => {
                    child.bit_decomposition_handles(input, bits)
                }
                RequestedBits::Ports { input, bits } => {
                    let (input, bits) = checked_bit_port_handles(child, input, bits)?;
                    child.bit_decomposition_handles(&input, &bits)
                }
            };
            let Some(relation) = certified(&relation)? else {
                return Ok(ComponentBitAmbiguityOutcome::NoCertificate(
                    NoBitAmbiguityCertificate::NoMatchingDecomposition,
                ));
            };
            let ports = ValidatedComponentPorts::new(facts, child, &instance, &ready)?;
            let caller_path = facts
                .unique_generation_path_with(budget, &constructors)
                .map_err(SummaryBlocker::LocalFacts)?;
            let child_path =
                child.unique_generation_path(budget).map_err(SummaryBlocker::LocalFacts)?;
            let caller_sites = facts.generated_component_equation_sites(budget, &ports);
            let child_sites = child.generated_equation_sites(budget);
            let completion = facts
                .generated_assignments(certified(&caller_sites)?, budget)
                .map_err(SummaryBlocker::LocalFacts)?;
            let equations = ClosureEquations {
                caller: certified(&caller_sites)?,
                completion: &completion,
                callee: certified(&child_sites)?,
                ports: &ports,
                ready: &ready,
                relation,
            };
            equations.check(facts, child, &caller_path, &child_path)?;
            prove_closure_models(self.field_context(), applied, &equations, budget)
        })
    }
}

fn checked_bit_port_handles(
    child: &AnalysisFacts<'_>,
    input: PortId,
    bits: PortId,
) -> Result<(AccessHandle, Vec<AccessHandle>), SummaryBlocker> {
    let input_port = child.hir().port(input).ok_or(SummaryBlocker::WrongInstance)?;
    let bit_port = child.hir().port(bits).ok_or(SummaryBlocker::WrongInstance)?;
    if input_port.schema != PortSchema::Signal
        || input_port.direction != Some(PortDirection::Input)
        || bit_port.schema != PortSchema::Signal
        || bit_port.direction != Some(PortDirection::Output)
    {
        return Err(SummaryBlocker::UnsupportedContext);
    }
    let input_handle =
        child.port_handle(input, &[]).map_err(|_| SummaryBlocker::UnsupportedContext)?;
    let bit_handles = child.rank_one_port_handles(bit_port, 512).map_err(|error| match error {
        RankOnePortError::WidthLimit => SummaryBlocker::ContextBudget,
        RankOnePortError::InvalidShape(_)
        | RankOnePortError::InvalidRank
        | RankOnePortError::InvalidHandle(_) => SummaryBlocker::UnsupportedContext,
    })?;
    Ok((input_handle, bit_handles))
}

#[cfg(test)]
mod tests;
