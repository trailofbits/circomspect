//! Must-bound component inputs through caller control-flow joins.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::{FlowGraph, NodeId};
use abstract_interpretation::lattice::Lattice;
use abstract_interpretation::solver::{
    solve, DataflowAnalysis, Forward, SolveResult, Transfer, TransferOutcome,
};
use parser::hir::{
    AccessPath, AccessStep, ArrayIndex, ControlGuard, Effect, ExprKind, PortId, PortSchema,
    SymbolKind,
};
use parser::new_frontend::PortDirection;

use crate::hir_cfg::{CfgEdge, CfgNode, CfgNodeKind, Origin};
use crate::hir_facts::{AccessKey, AnalysisFacts, FieldValue, InstanceRelation, Range, VisitAccesses};
use crate::interprocedural::component::AppliedComponentPort;
use crate::interprocedural::output_enumeration::EnumeratedComponentInstance;
use crate::interprocedural::summary::certified;
use crate::interprocedural::{ContextEvidence, SummaryBlocker};

/// An element identity only; catalog membership supplies its checked port bounds.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct InputPortElement {
    port: PortId,
    indices: Vec<usize>,
}

impl From<PortId> for InputPortElement {
    fn from(port: PortId) -> Self {
        Self { port, indices: Vec::new() }
    }
}

impl InputPortElement {
    pub(super) const fn port(&self) -> PortId {
        self.port
    }

    pub(super) fn indices(&self) -> &[usize] {
        &self.indices
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum GeneratedInputValue {
    Constant(FieldValue),
    ParentSignal(AccessKey),
}

#[derive(Clone, Copy)]
enum BindingPolicy {
    FixedOutput,
    CompleteModels,
    WitnessInputs,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum WitnessInputValue {
    Constant(FieldValue),
    ParentSignal(AccessKey),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum BindingValue {
    Generated(GeneratedInputValue),
    Witness(WitnessInputValue),
}

enum BindingSource {
    Generated,
    Witness,
}

impl TryFrom<BindingValue> for GeneratedInputValue {
    type Error = SummaryBlocker;

    fn try_from(value: BindingValue) -> Result<Self, Self::Error> {
        match value {
            BindingValue::Generated(value) => Ok(value),
            BindingValue::Witness(_) => Err(SummaryBlocker::WitnessOnlyInput),
        }
    }
}

impl TryFrom<BindingValue> for WitnessInputValue {
    type Error = SummaryBlocker;

    fn try_from(value: BindingValue) -> Result<Self, Self::Error> {
        match value {
            BindingValue::Witness(value) => Ok(value),
            BindingValue::Generated(_) => Err(SummaryBlocker::UnsupportedContext),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum InputState {
    Absent,
    Bound { value: BindingValue, sites: BTreeSet<NodeId> },
}

enum BindingJoin {
    Compatible,
    Conflict,
}

impl InputState {
    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Absent, Self::Absent) => true,
            (
                Self::Bound { value: left, sites: left_sites },
                Self::Bound { value: right, sites: right_sites },
            ) => left == right && left_sites.is_subset(right_sites),
            (Self::Absent, Self::Bound { .. }) | (Self::Bound { .. }, Self::Absent) => false,
        }
    }

    fn join_assign(&mut self, other: &Self) -> BindingJoin {
        match (&mut *self, other) {
            (
                Self::Bound { value: left, sites: left_sites },
                Self::Bound { value: right, sites: right_sites },
            ) if left == right => {
                left_sites.extend(right_sites);
                BindingJoin::Compatible
            }
            (Self::Absent, Self::Absent) => BindingJoin::Compatible,
            _ => BindingJoin::Conflict,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
/// Must evidence: an absent binding conflicts with a bound one, and equal
/// bindings join their finite sets of source sites. Invalid is the top state.
/// The selected field and finite CFG bound the height; solver budgets still
/// produce incomplete results before large dynamic paths can certify facts.
enum RelationState {
    Unreachable,
    Reached { instantiated: bool, inputs: BTreeMap<InputPortElement, InputState> },
    Invalid,
}

impl RelationState {
    fn boundary(inputs: &[InputPortElement]) -> Self {
        let inputs = inputs.iter().cloned().map(|port| (port, InputState::Absent)).collect();
        Self::Reached { instantiated: false, inputs }
    }

    fn invalidate(&mut self) {
        *self = Self::Invalid;
    }

    fn ready(&self) -> bool {
        let Self::Reached { instantiated, inputs } = self else { return false };
        *instantiated
            && inputs.values().all(|value| match value {
                InputState::Bound { .. } => true,
                InputState::Absent => false,
            })
    }
}

impl Lattice for RelationState {
    fn bottom() -> Self {
        Self::Unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unreachable, _) => true,
            (_, Self::Invalid) => true,
            (Self::Invalid, Self::Unreachable | Self::Reached { .. })
            | (Self::Reached { .. }, Self::Unreachable) => false,
            (
                Self::Reached { instantiated: left, inputs: left_inputs },
                Self::Reached { instantiated: right, inputs: right_inputs },
            ) => {
                (*left || !*right)
                    && left_inputs.len() == right_inputs.len()
                    && left_inputs.iter().all(|(port, state)| {
                        right_inputs.get(port).is_some_and(|other| state.leq(other))
                    })
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
        if let Self::Invalid = self {
            return false;
        }
        if let Self::Invalid = other {
            *self = Self::Invalid;
            return true;
        }
        let old = self.clone();
        let mut conflict = false;
        if let (
            Self::Reached { instantiated: left, inputs: left_inputs },
            Self::Reached { instantiated: right, inputs: right_inputs },
        ) = (&mut *self, other)
        {
            *left &= *right;
            conflict = left_inputs.keys().ne(right_inputs.keys());
            for (port, state) in left_inputs.iter_mut() {
                if let Some(other) = right_inputs.get(port) {
                    if let BindingJoin::Conflict = state.join_assign(other) {
                        conflict = true;
                    }
                }
            }
        }
        if conflict {
            *self = Self::Invalid;
        }
        *self != old
    }
}

#[derive(Clone, Debug)]
pub(super) struct CheckedInputBinding<Value> {
    pub(super) target: AccessKey,
    pub(super) value: Value,
    pub(super) origins: Vec<Origin>,
}

type ConstrainedInputBinding = CheckedInputBinding<GeneratedInputValue>;
type WitnessInputBinding = CheckedInputBinding<WitnessInputValue>;

struct ReadyInputs {
    bindings: BTreeMap<InputPortElement, CheckedInputBinding<BindingValue>>,
}

impl ReadyInputs {
    fn into_bindings<Value>(
        self,
    ) -> Result<BTreeMap<InputPortElement, CheckedInputBinding<Value>>, SummaryBlocker>
    where
        Value: TryFrom<BindingValue, Error = SummaryBlocker>,
    {
        let mut bindings = BTreeMap::new();
        for (port, binding) in self.bindings {
            bindings.insert(
                port,
                CheckedInputBinding {
                    target: binding.target,
                    value: Value::try_from(binding.value)?,
                    origins: binding.origins,
                },
            );
        }
        Ok(bindings)
    }
}

/// Initialization evidence only. No field equality follows from these bindings.
pub(super) struct ReadyWitnessInputs {
    caller: ContextEvidence,
    instance: EnumeratedComponentInstance,
    bindings: BTreeMap<InputPortElement, WitnessInputBinding>,
}

impl ReadyWitnessInputs {
    pub(super) fn caller(&self) -> &ContextEvidence {
        &self.caller
    }

    pub(super) fn binding(&self, port: PortId) -> Option<&WitnessInputBinding> {
        self.bindings.get(&port.into())
    }

    pub(super) fn matches(
        &self,
        facts: &AnalysisFacts<'_>,
        instance: &EnumeratedComponentInstance,
    ) -> bool {
        self.instance == *instance
            && facts.matches_evidence(&self.caller)
            && facts.reachable_node(facts.cfg().exit()).certified() == Some(&true)
    }
}

pub(super) struct ReadyInstanceAtUse {
    bindings: BTreeMap<InputPortElement, ConstrainedInputBinding>,
}

impl TryFrom<ReadyInputs> for ReadyInstanceAtUse {
    type Error = SummaryBlocker;

    fn try_from(ready: ReadyInputs) -> Result<Self, Self::Error> {
        Ok(Self { bindings: ready.into_bindings()? })
    }
}

impl ReadyInstanceAtUse {
    pub(super) fn bindings(&self) -> &BTreeMap<InputPortElement, ConstrainedInputBinding> {
        &self.bindings
    }

    pub(super) fn binding(&self, port: PortId) -> Option<&ConstrainedInputBinding> {
        self.bindings.get(&port.into())
    }
}

struct RelationAnalysis<'a> {
    facts: &'a AnalysisFacts<'a>,
    instance: &'a AccessPath,
    instantiation: NodeId,
    inputs: Vec<InputPortElement>,
    policy: BindingPolicy,
}

impl DataflowAnalysis<crate::hir_cfg::DefinitionCfg> for RelationAnalysis<'_> {
    type State = RelationState;
    type Reason = SummaryBlocker;

    fn boundary(&self, _: NodeId) -> Self::State {
        RelationState::boundary(&self.inputs)
    }
}

impl Transfer<RelationAnalysis<'_>, RelationState, SummaryBlocker> for CfgNode {
    fn apply(
        &self,
        analysis: &RelationAnalysis<'_>,
        input: &RelationState,
    ) -> TransferOutcome<RelationState, SummaryBlocker> {
        analysis.transfer_node(self, input)
    }
}

impl Transfer<RelationAnalysis<'_>, RelationState, SummaryBlocker> for CfgEdge {
    fn apply(
        &self,
        analysis: &RelationAnalysis<'_>,
        input: &RelationState,
    ) -> TransferOutcome<RelationState, SummaryBlocker> {
        let Some(edge) = analysis.facts.cfg().edge(self.id) else {
            return TransferOutcome::Opaque {
                provisional: input.clone(),
                reason: SummaryBlocker::ExternalSummary,
            };
        };
        match analysis.facts.reachable_node(edge.target).certified() {
            Some(true) => TransferOutcome::Known(input.clone()),
            Some(false) => TransferOutcome::Known(RelationState::Unreachable),
            None => TransferOutcome::Opaque {
                provisional: input.clone(),
                reason: SummaryBlocker::ExternalSummary,
            },
        }
    }
}

impl RelationAnalysis<'_> {
    fn transfer_node(
        &self,
        node: &CfgNode,
        input: &RelationState,
    ) -> TransferOutcome<RelationState, SummaryBlocker> {
        let mut state = input.clone();
        if let RelationState::Unreachable | RelationState::Invalid = state {
            return TransferOutcome::Known(state);
        }
        let result = match &node.kind {
            CfgNodeKind::Instantiate { .. } if node.id == self.instantiation => {
                if let RelationState::Reached { instantiated, .. } = &mut state {
                    *instantiated = true;
                }
                Ok(())
            }
            CfgNodeKind::Witness { target, value } => {
                self.bind_witness(node, target, *value, &mut state)
            }
            CfgNodeKind::Constraint { target: None, left, right } => {
                self.check_competing_equality(*left, *right, &mut state)
            }
            CfgNodeKind::Evaluate(expression) => self.check_read(*expression, &mut state),
            CfgNodeKind::Branch { guard, .. } => Self::check_guard(*guard, &mut state),
            CfgNodeKind::LoopHeader => {
                state.invalidate();
                Err(SummaryBlocker::UnsupportedContext)
            }
            CfgNodeKind::Opaque(_)
            | CfgNodeKind::OpaqueAssignment { .. }
            | CfgNodeKind::OpaqueEquality { .. } => {
                state.invalidate();
                Err(SummaryBlocker::ExternalSummary)
            }
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::Constraint { target: Some(_), .. }
            | CfgNodeKind::Assignment { .. }
            | CfgNodeKind::DeferredAssignment { .. }
            | CfgNodeKind::Update { .. }
            | CfgNodeKind::Instantiate { .. }
            | CfgNodeKind::Declaration { .. }
            | CfgNodeKind::Return(_)
            | CfgNodeKind::Assert { .. }
            | CfgNodeKind::DeferredAssert { .. }
            | CfgNodeKind::Log => Ok(()),
        };
        match result {
            Ok(()) => TransferOutcome::Known(state),
            Err(reason) => TransferOutcome::Opaque { provisional: state, reason },
        }
    }

    fn check_guard(guard: ControlGuard, state: &mut RelationState) -> Result<(), SummaryBlocker> {
        match guard {
            ControlGuard::CheckedCompileTime => Ok(()),
            ControlGuard::DeferredScalar | ControlGuard::WitnessOnly => {
                state.invalidate();
                Err(SummaryBlocker::UnsupportedContext)
            }
        }
    }

    fn bind_witness(
        &self,
        node: &CfgNode,
        target: &AccessPath,
        value: parser::hir::ExprId,
        state: &mut RelationState,
    ) -> Result<(), SummaryBlocker> {
        if target.root != self.instance.root {
            return Ok(());
        }
        let relation = self.facts.instance_path_relation(self.instance, target);
        if relation == InstanceRelation::Separate {
            return Ok(());
        }
        let (port, indices) = self
            .facts
            .source_component_port_indices(target)
            .map_err(|_| SummaryBlocker::UnsupportedContext)?;
        let port = InputPortElement { port, indices };
        self.bind_input(node, port, relation, value, state)
    }

    fn bind_input(
        &self,
        node: &CfgNode,
        port: InputPortElement,
        relation: InstanceRelation,
        value: parser::hir::ExprId,
        state: &mut RelationState,
    ) -> Result<(), SummaryBlocker> {
        let RelationState::Reached { instantiated, inputs, .. } = state else {
            return Ok(());
        };
        let Some(binding) = inputs.get_mut(&port) else {
            state.invalidate();
            return Err(SummaryBlocker::ExternalSummary);
        };
        if relation != InstanceRelation::Exact || !*instantiated {
            state.invalidate();
            return Err(if relation == InstanceRelation::Possible {
                SummaryBlocker::SymbolicInstance
            } else {
                SummaryBlocker::ExternalSummary
            });
        }
        let value = self.checked_binding_value(node, value)?;
        match binding {
            InputState::Absent => {
                *binding = InputState::Bound { value, sites: BTreeSet::from([node.id]) };
            }
            InputState::Bound { .. } => {
                state.invalidate();
                return Err(SummaryBlocker::DuplicateInputBinding);
            }
        }
        Ok(())
    }

    fn checked_binding_value(
        &self,
        node: &CfgNode,
        value: parser::hir::ExprId,
    ) -> Result<BindingValue, SummaryBlocker> {
        match (self.policy, self.binding_source(node, value)?) {
            (BindingPolicy::WitnessInputs, BindingSource::Witness) => {
                return self.checked_witness_value(value).map(BindingValue::Witness);
            }
            (BindingPolicy::WitnessInputs, BindingSource::Generated) => {
                return Err(SummaryBlocker::UnsupportedContext);
            }
            (
                BindingPolicy::FixedOutput | BindingPolicy::CompleteModels,
                BindingSource::Witness,
            ) => {
                return Err(SummaryBlocker::WitnessOnlyInput);
            }
            (
                BindingPolicy::FixedOutput | BindingPolicy::CompleteModels,
                BindingSource::Generated,
            ) => {}
        }
        if let BindingPolicy::CompleteModels = self.policy {
            if let Some(key) = self.parent_signal(value)? {
                return Ok(BindingValue::Generated(GeneratedInputValue::ParentSignal(key)));
            }
        }
        let range = self.facts.range(value);
        let Range::Exact(value) = certified(&range)? else {
            return Err(SummaryBlocker::UnsupportedContext);
        };
        let fixed = self.facts.generated_assignment_constant(node.id);
        if certified(&fixed)?.as_ref() != Some(value) {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        Ok(BindingValue::Generated(GeneratedInputValue::Constant(value.clone())))
    }

    fn binding_source(
        &self,
        node: &CfgNode,
        expression: parser::hir::ExprId,
    ) -> Result<BindingSource, SummaryBlocker> {
        let origin = node.origin.ok_or(SummaryBlocker::ExternalSummary)?;
        let effect = self
            .facts
            .hir()
            .block(origin.block)
            .and_then(|block| block.effects.get(origin.effect_index))
            .ok_or(SummaryBlocker::ExternalSummary)?;
        let (source, value, provenance) = match effect {
            Effect::ConstraintAssignment { target, value, .. } => {
                (target, value, BindingSource::Generated)
            }
            Effect::WitnessAssignment { target, value, .. } => {
                (target, value, BindingSource::Witness)
            }
            Effect::Declaration { .. }
            | Effect::VariableAssignment { .. }
            | Effect::DeferredVariableAssignment { .. }
            | Effect::ComponentInstantiation { .. }
            | Effect::OpaqueAssignment { .. }
            | Effect::EqualityConstraint { .. }
            | Effect::OpaqueEquality { .. }
            | Effect::Update { .. }
            | Effect::If { .. }
            | Effect::While { .. }
            | Effect::For { .. }
            | Effect::Return { .. }
            | Effect::Assert { .. }
            | Effect::DeferredAssert { .. }
            | Effect::Log { .. }
            | Effect::AnonymousComponent { .. }
            | Effect::Block(_)
            | Effect::Opaque { .. } => {
                return Err(SummaryBlocker::ExternalSummary);
            }
        };
        let CfgNodeKind::Witness { target, value: node_value } = &node.kind else {
            return Err(SummaryBlocker::ExternalSummary);
        };
        if source != target || value != node_value || *value != expression {
            return Err(SummaryBlocker::ExternalSummary);
        }
        Ok(provenance)
    }

    fn checked_witness_value(
        &self,
        value: parser::hir::ExprId,
    ) -> Result<WitnessInputValue, SummaryBlocker> {
        if let Some(key) = self.parent_signal(value)? {
            return Ok(WitnessInputValue::ParentSignal(key));
        }
        let range = self.facts.range(value);
        let Range::Exact(value) = certified(&range)? else {
            return Err(SummaryBlocker::UnsupportedContext);
        };
        Ok(WitnessInputValue::Constant(value.clone()))
    }

    fn parent_signal(
        &self,
        value: parser::hir::ExprId,
    ) -> Result<Option<AccessKey>, SummaryBlocker> {
        let Some(ExprKind::Access(path)) =
            self.facts.hir().expression(value).map(|expression| &expression.kind)
        else {
            return Ok(None);
        };
        let symbol = self.facts.hir().symbol(path.root).ok_or(SummaryBlocker::ForeignDefinition)?;
        if symbol.kind == SymbolKind::Signal && path.root == path.terminal {
            return Ok(Some(certified(&self.facts.exact_access_key(path))?.clone()));
        }
        Ok(None)
    }

    fn check_read(
        &self,
        expression: parser::hir::ExprId,
        state: &mut RelationState,
    ) -> Result<(), SummaryBlocker> {
        let Some(expr) = self.facts.hir().expression(expression) else {
            return Err(SummaryBlocker::ExternalSummary);
        };
        let ExprKind::Access(path) = &expr.kind else { return Ok(()) };
        if !path.component_output {
            return Ok(());
        }
        match self.facts.instance_path_relation(self.instance, path) {
            InstanceRelation::Separate => {}
            InstanceRelation::Exact if state.ready() => {}
            InstanceRelation::Exact | InstanceRelation::Possible => {
                state.invalidate();
            }
        }
        Ok(())
    }

    fn check_competing_equality(
        &self,
        left: parser::hir::ExprId,
        right: Option<parser::hir::ExprId>,
        state: &mut RelationState,
    ) -> Result<(), SummaryBlocker> {
        if let BindingPolicy::CompleteModels = self.policy {
            return Ok(());
        }
        for expression in [Some(left), right].into_iter().flatten() {
            let mut touches = false;
            if !expression.visit_accesses(self.facts.hir(), &mut |path| {
                touches |= self.facts.instance_path_relation(self.instance, path)
                    != InstanceRelation::Separate;
            }) {
                state.invalidate();
                return Err(SummaryBlocker::ExternalSummary);
            }
            if touches {
                state.invalidate();
                return Err(SummaryBlocker::ExternalSummary);
            }
        }
        Ok(())
    }
}

pub(super) fn ready_instance_at_use(
    facts: &AnalysisFacts<'_>,
    applied: &AppliedComponentPort,
    child: parser::hir::TemplateId,
) -> Result<ReadyInstanceAtUse, SummaryBlocker> {
    let Some(CfgNodeKind::Instantiate { target, .. }) =
        facts.cfg().node(applied.instantiation()).map(|node| &node.kind)
    else {
        return Err(SummaryBlocker::WrongInstance);
    };
    if facts.instance_relation(applied.handle(), target) != InstanceRelation::Exact {
        return Err(SummaryBlocker::WrongInstance);
    }
    ready_inputs(
        facts,
        applied.handle().path(),
        applied.instantiation(),
        child,
        BindingPolicy::FixedOutput,
    )
    .and_then(ReadyInstanceAtUse::try_from)
}

pub(super) fn ready_enumerated_instance(
    facts: &AnalysisFacts<'_>,
    instance: &EnumeratedComponentInstance,
) -> Result<ReadyInstanceAtUse, SummaryBlocker> {
    ready_enumerated_inputs(facts, instance, BindingPolicy::FixedOutput)
        .and_then(ReadyInstanceAtUse::try_from)
}

pub(super) fn ready_model_instance(
    facts: &AnalysisFacts<'_>,
    instance: &EnumeratedComponentInstance,
) -> Result<ReadyInstanceAtUse, SummaryBlocker> {
    ready_enumerated_inputs(facts, instance, BindingPolicy::CompleteModels)
        .and_then(ReadyInstanceAtUse::try_from)
}

pub(super) fn ready_witness_instance(
    facts: &AnalysisFacts<'_>,
    caller: &ContextEvidence,
    instance: &EnumeratedComponentInstance,
) -> Result<ReadyWitnessInputs, SummaryBlocker> {
    if !facts.matches_evidence(caller)
        || facts.reachable_node(facts.cfg().exit()).certified() != Some(&true)
    {
        return Err(SummaryBlocker::WrongContext);
    }
    let ready = ready_enumerated_inputs(facts, instance, BindingPolicy::WitnessInputs)?;
    Ok(ReadyWitnessInputs {
        caller: caller.clone(),
        instance: instance.clone(),
        bindings: ready.into_bindings()?,
    })
}

fn ready_enumerated_inputs(
    facts: &AnalysisFacts<'_>,
    instance: &EnumeratedComponentInstance,
    policy: BindingPolicy,
) -> Result<ReadyInputs, SummaryBlocker> {
    let parser::hir::DefinitionRef::Template(child) = instance.callee.context().definition() else {
        return Err(SummaryBlocker::WrongInstance);
    };
    let Some(CfgNodeKind::Instantiate { target, .. }) =
        facts.cfg().node(instance.instantiation).map(|node| &node.kind)
    else {
        return Err(SummaryBlocker::WrongInstance);
    };
    if target != &instance.target {
        return Err(SummaryBlocker::WrongInstance);
    }
    let steps = instance
        .indices
        .iter()
        .map(|index| AccessStep::Index {
            index: ArrayIndex::Constant(index.to_string()),
            span: target.span,
        })
        .collect();
    let exact = AccessPath { steps, ..target.clone() };
    ready_inputs(facts, &exact, instance.instantiation, child, policy)
}

fn ready_inputs(
    facts: &AnalysisFacts<'_>,
    instance: &AccessPath,
    instantiation: NodeId,
    child: parser::hir::TemplateId,
    policy: BindingPolicy,
) -> Result<ReadyInputs, SummaryBlocker> {
    let inputs = input_ports(facts, child)?;
    let analysis = RelationAnalysis { facts, instance, instantiation, inputs, policy };
    let result = solve::<_, _, Forward>(facts.cfg(), &analysis, Some(100_000))
        .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
    let states = match result {
        SolveResult::Complete(states) => states,
        SolveResult::Incomplete { blockers, .. } => {
            for blocker in &blockers {
                if let abstract_interpretation::solver::Blocker::OpaqueNode { reason, .. } = blocker
                {
                    return Err(reason.clone());
                }
            }
            return Err(SummaryBlocker::ContextBudget);
        }
    };
    let state = states
        .get(&facts.cfg().exit())
        .and_then(|item| item.output.as_ref())
        .ok_or(SummaryBlocker::ExternalSummary)?;
    let RelationState::Reached { instantiated: true, inputs } = state else {
        return Err(SummaryBlocker::ExternalSummary);
    };
    let mut bindings = BTreeMap::new();
    for (port, binding) in inputs {
        bindings.insert(port.clone(), checked_binding(facts, binding)?);
    }
    Ok(ReadyInputs { bindings })
}

fn input_ports(
    facts: &AnalysisFacts<'_>,
    child: parser::hir::TemplateId,
) -> Result<Vec<InputPortElement>, SummaryBlocker> {
    let template = facts.hir().template(child).ok_or(SummaryBlocker::ForeignDefinition)?;
    let mut inputs = Vec::new();
    for id in &template.ports {
        let port = facts.hir().port(*id).ok_or(SummaryBlocker::ForeignDefinition)?;
        if port.direction != Some(PortDirection::Input) {
            continue;
        }
        let symbol = facts.hir().symbol(port.symbol).ok_or(SummaryBlocker::ForeignDefinition)?;
        if symbol.rank != 0 || port.schema != PortSchema::Signal {
            return Err(SummaryBlocker::UnsupportedContext);
        }
        inputs.push((*id).into());
    }
    Ok(inputs)
}

fn checked_binding(
    facts: &AnalysisFacts<'_>,
    binding: &InputState,
) -> Result<CheckedInputBinding<BindingValue>, SummaryBlocker> {
    let InputState::Bound { value, sites } = binding else {
        return Err(SummaryBlocker::MissingInputBinding);
    };
    let mut origins = Vec::new();
    let mut target_key = None;
    for id in sites {
        let Some(CfgNodeKind::Witness { target, .. }) =
            facts.cfg().node(*id).map(|node| &node.kind)
        else {
            return Err(SummaryBlocker::ExternalSummary);
        };
        let key = certified(&facts.exact_access_key(target))?.clone();
        if target_key.as_ref().is_some_and(|previous| previous != &key) {
            return Err(SummaryBlocker::WrongInstance);
        }
        target_key = Some(key);
        let origin = facts
            .cfg()
            .node(*id)
            .and_then(|node| node.origin)
            .ok_or(SummaryBlocker::ExternalSummary)?;
        if !origins.contains(&origin) {
            origins.push(origin);
        }
    }
    if origins.is_empty() {
        return Err(SummaryBlocker::ExternalSummary);
    }
    Ok(CheckedInputBinding {
        target: target_key.ok_or(SummaryBlocker::MissingInputBinding)?,
        value: value.clone(),
        origins,
    })
}

#[cfg(test)]
mod tests {
    use abstract_interpretation::graph::{FlowGraph, NodeId};
    use abstract_interpretation::lattice::Lattice;
    use abstract_interpretation::solver::{Transfer, TransferOutcome};
    use parser::hir::{lift_project, DefinitionRef, PortId};
    use parser::new_frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::build_cfg;
    use crate::hir_facts::{FieldContext, FieldValue};
    use crate::interprocedural::{CallOwner, CallReachability, ProjectSummaries};

    use crate::interprocedural::input_relation::{
        BindingPolicy, BindingValue, GeneratedInputValue, InputPortElement, InputState,
        RelationAnalysis, RelationState, SummaryBlocker, WitnessInputValue,
    };
    use std::collections::{BTreeMap, BTreeSet};

    fn samples(
        port: PortId,
        other: PortId,
        seven: FieldValue,
        eight: FieldValue,
    ) -> Vec<RelationState> {
        let first = BTreeSet::from([NodeId::new(3)]);
        let both = BTreeSet::from([NodeId::new(3), NodeId::new(5)]);
        let inputs = [
            InputState::Absent,
            InputState::Bound {
                value: BindingValue::Generated(GeneratedInputValue::Constant(seven.clone())),
                sites: first,
            },
            InputState::Bound {
                value: BindingValue::Generated(GeneratedInputValue::Constant(seven.clone())),
                sites: both,
            },
            InputState::Bound {
                value: BindingValue::Generated(GeneratedInputValue::Constant(eight)),
                sites: BTreeSet::from([NodeId::new(4)]),
            },
            InputState::Bound {
                value: BindingValue::Witness(WitnessInputValue::Constant(seven)),
                sites: BTreeSet::from([NodeId::new(3)]),
            },
        ];
        let mut states = vec![RelationState::Unreachable, RelationState::Invalid];
        for input in inputs {
            for instantiated in [false, true] {
                states.push(RelationState::Reached {
                    instantiated,
                    inputs: BTreeMap::from([(port.into(), input.clone())]),
                });
            }
        }
        states.push(RelationState::Reached {
            instantiated: true,
            inputs: BTreeMap::from([(other.into(), InputState::Absent)]),
        });
        states.push(RelationState::Reached {
            instantiated: true,
            inputs: BTreeMap::from([(
                InputPortElement { port, indices: vec![0] },
                InputState::Absent,
            )]),
        });
        states
    }

    fn state(outcome: TransferOutcome<RelationState, SummaryBlocker>) -> RelationState {
        match outcome {
            TransferOutcome::Known(state) | TransferOutcome::Opaque { provisional: state, .. } => {
                state
            }
        }
    }

    #[test]
    fn must_binding_lattice_and_real_cfg_transfers_are_monotone() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-relation-laws-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let file = directory.join("case.circom");
        std::fs::write(
            &file,
            "template Child(){signal input in;signal output out;out<==in;} \
             template Parent(){component c=Child();if(1 << 1){c.in<==7;}else{c.in<==7;} \
             signal output y;y<==c.out;}",
        )
        .unwrap();
        let loaded = load_sources(&[file], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let parent = lifted.hir.definition("Parent").unwrap();
        let DefinitionRef::Template(child) = lifted.hir.definition("Child").unwrap() else {
            panic!("Child must be a template")
        };
        let ports = &lifted.hir.template(child).unwrap().ports;
        let cfg = build_cfg(&lifted.hir, parent).unwrap();
        let caller = provider.symbolic_root(parent).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &caller, None).unwrap();
        let handle = facts
            .component_output_handle(lifted.hir.components()[0].id, &[], ports[1], &[])
            .unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
        let CallReachability::Reachable(call) = provider.graph().reachable_call(site.id(), &facts)
        else {
            panic!("Child must be reachable")
        };
        let applied = provider.apply_component_output(&facts, &caller, &call, &handle);
        let applied = applied.certified().unwrap();
        let crate::hir_cfg::CfgNodeKind::Instantiate { target, .. } =
            &facts.cfg().node(applied.instantiation()).unwrap().kind
        else {
            panic!("expected a checked instantiation");
        };
        let analysis = RelationAnalysis {
            facts: &facts,
            instance: target,
            instantiation: applied.instantiation(),
            inputs: vec![ports[0].into()],
            policy: BindingPolicy::FixedOutput,
        };
        let field = FieldContext::for_curve(Curve::Bn254);
        let states =
            samples(ports[0], ports[1], field.canonical(7.into()), field.canonical(8.into()));
        check_lattice_laws(&states);
        check_transfer_monotonicity(&cfg, &analysis, &states);
    }

    fn check_lattice_laws(states: &[RelationState]) {
        for left in states {
            for right in states {
                let mut idempotent = left.clone();
                idempotent.join_assign(left);
                assert_eq!(&idempotent, left);
                let mut join = left.clone();
                join.join_assign(right);
                assert!(left.leq(&join) && right.leq(&join));
                let mut reverse = right.clone();
                reverse.join_assign(left);
                assert_eq!(join, reverse);
                for third in states {
                    let mut left_grouped = join.clone();
                    left_grouped.join_assign(third);
                    let mut tail = right.clone();
                    tail.join_assign(third);
                    let mut right_grouped = left.clone();
                    right_grouped.join_assign(&tail);
                    assert_eq!(left_grouped, right_grouped);
                }
            }
        }
    }

    fn check_transfer_monotonicity(
        cfg: &crate::hir_cfg::DefinitionCfg,
        analysis: &RelationAnalysis<'_>,
        states: &[RelationState],
    ) {
        for left in states {
            for right in states {
                if !left.leq(right) {
                    continue;
                }
                for id in cfg.nodes() {
                    let node = cfg.node(*id).unwrap();
                    let before = state(node.apply(analysis, left));
                    let after = state(node.apply(analysis, right));
                    assert!(before.leq(&after), "node {id:?}: {left:?} <= {right:?}");
                }
                for id in cfg.edges() {
                    let edge = cfg.edge(*id).unwrap();
                    let before = state(edge.payload.apply(analysis, left));
                    let after = state(edge.payload.apply(analysis, right));
                    assert!(before.leq(&after), "edge {id:?}: {left:?} <= {right:?}");
                }
            }
        }
    }
}

#[cfg(test)]
mod witness_tests;
