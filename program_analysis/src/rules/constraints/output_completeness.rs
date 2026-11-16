//! Declared output elements without a witness write or generated constraint.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use num_traits::ToPrimitive;
use parser::frontend::PortDirection;
use parser::hir::{DefinitionRef, PortId, SymbolId};

use crate::hir_cfg::CfgNodeKind;
use crate::hir_facts::{Incidence, Range};
use crate::interprocedural::ContextOrigin;
use crate::rules::{AbstentionReason, Rule, RuleContext, RuleKind, RuleResult};

pub(super) struct OutputCompleteness;

impl Rule for OutputCompleteness {
    fn kind(&self) -> RuleKind {
        RuleKind::UnassignedOutput
    }

    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
        let mut result = RuleResult::default();
        let DefinitionRef::Template(id) = context.call_context().definition() else {
            return result;
        };
        if let Err(blocker) = context.validated_definition() {
            if let Ok(header) = context.validated_header() {
                result.add_abstention(context.abstention(
                    self.kind(),
                    header.name_span(),
                    AbstentionReason::Summary(BTreeSet::from([blocker])),
                ));
            }
            return result;
        }
        let Some(template) = context.hir().template(id) else { return result };
        if template.custom || template.external {
            return result;
        }
        for id in &template.ports {
            let Some(port) = context.hir().port(*id) else { continue };
            if port.direction == Some(PortDirection::Output) {
                inspect_port(context, *id, &mut result);
            }
        }
        result
    }
}

#[derive(Default)]
struct Writes {
    all: bool,
    exact: BTreeSet<Vec<usize>>,
    unknown: bool,
}

#[derive(Clone, Copy)]
enum OutputProblem {
    NoWitness,
    NeverAssigned,
    MultipleNeverAssigned(usize),
    Unconstrained,
    MultipleUnconstrained(usize),
}

impl OutputProblem {
    fn message(self) -> String {
        match self {
            Self::NoWitness => "has no witness assignment".into(),
            Self::NeverAssigned => "is never assigned".into(),
            Self::MultipleNeverAssigned(count) => format!("has {count} unassigned elements"),
            Self::Unconstrained => "has no generated constraint".into(),
            Self::MultipleUnconstrained(count) => {
                format!("has {count} elements without generated constraints")
            }
        }
    }

    fn comment(self, path: &str, name: &str) -> String {
        match self {
            Self::NoWitness | Self::NeverAssigned => {
                format!("The signal `{path}` has no witness assignment.")
            }
            Self::MultipleNeverAssigned(_) => {
                format!("Multiple elements in `{name}` are unassigned.")
            }
            Self::MultipleUnconstrained(_) => {
                format!("Multiple elements in `{name}` are unconstrained.")
            }
            Self::Unconstrained => format!("The signal `{path}` is never constrained."),
        }
    }
}

fn inspect_port(context: &RuleContext<'_, '_, '_>, port_id: PortId, result: &mut RuleResult) {
    let Some(port) = context.hir().port(port_id) else { return };
    let Some(symbol) = context.hir().symbol(port.symbol) else { return };
    let writes = collect_writes(context, port.symbol);
    let no_witness = !writes.all && writes.exact.is_empty() && !writes.unknown;
    let called = match context.origin() {
        ContextOrigin::Call(_) => true,
        ContextOrigin::SymbolicRoot | ContextOrigin::Main(_) => false,
    };
    if no_witness && called {
        return;
    }
    let Some(indices) = output_indices(context, port.symbol) else {
        if no_witness {
            report(context, result, port_id, &symbol.name, None, OutputProblem::NoWitness);
        }
        abstain(context, result, port.span);
        return;
    };
    if no_witness {
        report_unwritten_port(context, result, port_id, &symbol.name, &indices);
    }
    let mut uncertain_write = false;
    let mut missing_assignments = Vec::new();
    let mut unconstrained = Vec::new();
    for index in indices {
        abstract_interpretation::timeout::check();
        if !no_witness && !writes.all && !writes.exact.contains(&index) {
            if writes.unknown {
                uncertain_write = true;
            } else {
                missing_assignments.push(index.clone());
            }
        }
        if let Some(Incidence::Zero) = constraint_incidence(context, result, port_id, &index) {
            unconstrained.push(index);
        }
    }
    match missing_assignments.as_slice() {
        [] => {}
        [index] => {
            report(
                context,
                result,
                port_id,
                &symbol.name,
                Some(index),
                OutputProblem::NeverAssigned,
            );
        }
        _ => report(
            context,
            result,
            port_id,
            &symbol.name,
            None,
            OutputProblem::MultipleNeverAssigned(missing_assignments.len()),
        ),
    }
    match unconstrained.as_slice() {
        [] => {}
        [index] => {
            report(
                context,
                result,
                port_id,
                &symbol.name,
                Some(index),
                OutputProblem::Unconstrained,
            );
        }
        _ => report(
            context,
            result,
            port_id,
            &symbol.name,
            None,
            OutputProblem::MultipleUnconstrained(unconstrained.len()),
        ),
    }
    if uncertain_write {
        abstain(context, result, port.span);
    }
}

fn report_unwritten_port(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    port: PortId,
    name: &str,
    indices: &[Vec<usize>],
) {
    match indices {
        [] => {}
        [index] if index.is_empty() => {
            report(context, result, port, name, None, OutputProblem::NoWitness);
        }
        [index] => {
            report(context, result, port, name, Some(index), OutputProblem::NeverAssigned);
        }
        _ => report(
            context,
            result,
            port,
            name,
            None,
            OutputProblem::MultipleNeverAssigned(indices.len()),
        ),
    }
}

fn collect_writes(context: &RuleContext<'_, '_, '_>, output: SymbolId) -> Writes {
    let mut writes = Writes::default();
    let blocked = context.facts().forward_blocked_descendants();
    for id in context.facts().cfg().nodes() {
        abstract_interpretation::timeout::check();
        let Some(node) = context.facts().cfg().node(*id) else {
            writes.unknown = true;
            continue;
        };
        let target = match &node.kind {
            CfgNodeKind::Witness { target, .. } | CfgNodeKind::OpaqueAssignment { target, .. }
                if target.root == output =>
            {
                target
            }
            CfgNodeKind::Opaque(_) => {
                writes.unknown = true;
                continue;
            }
            _ => continue,
        };
        match context.facts().reachable_node_from_blockers(*id, &blocked) {
            Some(false) => continue,
            Some(true) => {}
            None => {
                writes.unknown = true;
                continue;
            }
        }
        if matches!(node.kind, CfgNodeKind::OpaqueAssignment { .. }) {
            writes.unknown = true;
        } else if target.steps.is_empty() {
            writes.all = true;
        } else {
            match context.facts().exact_access_key_at(target, *id).into_result() {
                Ok(key) => match key.local_array_indices() {
                    Some(indices) => {
                        writes.exact.insert(indices);
                    }
                    None => writes.unknown = true,
                },
                Err(_) => writes.unknown = true,
            }
        }
    }
    writes
}

fn output_indices(context: &RuleContext<'_, '_, '_>, output: SymbolId) -> Option<Vec<Vec<usize>>> {
    let symbol = context.hir().symbol(output)?;
    let mut indices = vec![Vec::new()];
    for dimension in &symbol.dimensions {
        let Range::Exact(size) = context.facts().range(*dimension).certified()?.clone() else {
            return None;
        };
        let size = size.as_bigint().to_usize()?;
        if indices.len().checked_mul(size)? > 10_000 {
            return None;
        }
        indices = indices
            .into_iter()
            .flat_map(|prefix| {
                (0..size).map(move |index| {
                    let mut path = prefix.clone();
                    path.push(index);
                    path
                })
            })
            .collect();
    }
    Some(indices)
}

fn constraint_incidence(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    port: PortId,
    indices: &[usize],
) -> Option<Incidence> {
    let source = context.hir().port(port)?;
    let Ok(handle) = context.facts().port_handle(port, indices) else {
        abstain(context, result, source.span);
        return None;
    };
    match context.facts().incidence_handle(&handle).into_result() {
        Ok(incidence) => {
            if incidence == Incidence::May {
                abstain(context, result, source.span);
            }
            Some(incidence)
        }
        Err(blockers) => {
            result.add_abstention(context.abstention(
                RuleKind::UnassignedOutput,
                source.span,
                AbstentionReason::LocalFacts(blockers),
            ));
            None
        }
    }
}

fn abstain(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    span: parser::frontend::Span,
) {
    result.add_abstention(context.abstention(
        RuleKind::UnassignedOutput,
        span,
        AbstentionReason::UnsupportedConstruct,
    ));
}

fn report(
    context: &RuleContext<'_, '_, '_>,
    result: &mut RuleResult,
    port: PortId,
    name: &str,
    indices: Option<&[usize]>,
    problem: OutputProblem,
) {
    let Some(port) = context.hir().port(port) else { return };
    let mut path = name.to_owned();
    if let Some(indices) = indices {
        for index in indices {
            path.push('[');
            path.push_str(&index.to_string());
            path.push(']');
        }
    }
    result.add_finding(context.finding(
        RuleKind::UnassignedOutput,
        format!("Output `{path}` {}.", problem.message()),
        port.span,
        problem.comment(&path, name),
    ));
}
