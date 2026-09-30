//! Backward may-liveness over the same immutable HIR CFG.

use std::collections::{BTreeMap, BTreeSet};

use abstract_interpretation::graph::NodeId;
use abstract_interpretation::lattice::Lattice;
use abstract_interpretation::solver::{DataflowAnalysis, Transfer, TransferOutcome};
use parser::hir::{DefinitionRef, ExprId, HirProject, SymbolId};
use parser::new_frontend::PortDirection;

use crate::hir_cfg::{CfgEdge, CfgNode, CfgNodeKind, DefinitionCfg, EdgeKind};

use super::access::{key_for_path, AccessKey};
use super::field::FieldContext;
use super::forward::eval_expression;
use super::walk::VisitAccesses;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LiveState {
    Unreachable,
    Reached(BTreeSet<AccessKey>),
}

// Liveness keys are drawn from the finite HIR access occurrences. Dynamic
// indices stay symbolic here, so loop iterations cannot create fresh keys.

impl LiveState {
    pub fn contains_alias(&self, query: &AccessKey) -> Option<bool> {
        let Self::Reached(items) = self else { return None };
        Some(items.iter().any(|item| item.may_alias(query)))
    }
}

impl Lattice for LiveState {
    fn bottom() -> Self {
        Self::Unreachable
    }

    fn leq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unreachable, _) => true,
            (Self::Reached(_), Self::Unreachable) => false,
            (Self::Reached(left), Self::Reached(right)) => left.is_subset(right),
        }
    }

    fn join_assign(&mut self, other: &Self) -> bool {
        match (&mut *self, other) {
            (Self::Unreachable, Self::Unreachable) | (Self::Reached(_), Self::Unreachable) => false,
            (state @ Self::Unreachable, Self::Reached(_)) => {
                *state = other.clone();
                true
            }
            (Self::Reached(left), Self::Reached(right)) => {
                let old_len = left.len();
                left.extend(right.iter().cloned());
                left.len() != old_len
            }
        }
    }
}

pub struct LivenessAnalysis<'a> {
    pub hir: &'a HirProject,
    pub field: &'a FieldContext,
    pub observable_outputs: BTreeSet<SymbolId>,
}

impl LivenessAnalysis<'_> {
    pub fn new<'a>(
        hir: &'a HirProject,
        field: &'a FieldContext,
        definition: DefinitionRef,
    ) -> LivenessAnalysis<'a> {
        let ports = match definition {
            DefinitionRef::Function(_) => &[][..],
            DefinitionRef::Template(id) => hir.template(id).map_or(&[][..], |item| &item.ports),
            DefinitionRef::Bus(id) => hir.bus(id).map_or(&[][..], |item| &item.ports),
        };
        let observable_outputs = ports
            .iter()
            .filter_map(|id| hir.port(*id))
            .filter(|port| port.direction == Some(PortDirection::Output))
            .map(|port| port.symbol)
            .collect();
        LivenessAnalysis { hir, field, observable_outputs }
    }
}

impl DataflowAnalysis<DefinitionCfg> for LivenessAnalysis<'_> {
    type State = LiveState;
    type Reason = String;

    fn boundary(&self, _: NodeId) -> Self::State {
        LiveState::Reached(BTreeSet::new())
    }
}

impl Transfer<LivenessAnalysis<'_>, LiveState, String> for CfgNode {
    fn apply(
        &self,
        analysis: &LivenessAnalysis<'_>,
        input: &LiveState,
    ) -> TransferOutcome<LiveState, String> {
        let mut output = input.clone();
        let LiveState::Reached(live) = &mut output else {
            return TransferOutcome::Known(output);
        };
        let empty = BTreeMap::new();
        let mut complete = true;
        match &self.kind {
            CfgNodeKind::Evaluate(expression) => {
                complete &= collect(analysis, *expression, live, &empty);
            }
            CfgNodeKind::Witness { target, .. } => {
                let key = key_for_path(analysis.hir, analysis.field, target, &empty);
                if analysis.observable_outputs.contains(&target.root) || target.component_input {
                    live.insert(key);
                } else if key.exact_alias(&key) {
                    live.remove(&key);
                }
            }
            CfgNodeKind::Assignment { target, .. } => {
                let key = key_for_path(analysis.hir, analysis.field, target, &empty);
                if key.exact_alias(&key) {
                    live.remove(&key);
                }
            }
            CfgNodeKind::Constraint { target, left, right } => {
                if let Some(target) = target {
                    live.insert(key_for_path(analysis.hir, analysis.field, target, &empty));
                }
                complete &= collect(analysis, *left, live, &empty);
                if let Some(right) = right {
                    complete &= collect(analysis, *right, live, &empty);
                }
            }
            CfgNodeKind::Branch(expression)
            | CfgNodeKind::Return(expression)
            | CfgNodeKind::Assert { condition: expression } => {
                complete &= collect(analysis, *expression, live, &empty);
            }
            CfgNodeKind::Opaque(reason) => {
                return TransferOutcome::Opaque {
                    provisional: output,
                    reason: format!("{reason:?}"),
                };
            }
            CfgNodeKind::Instantiate { .. } => {
                return TransferOutcome::Opaque {
                    provisional: output,
                    reason: "external component summary".into(),
                };
            }
            CfgNodeKind::Entry
            | CfgNodeKind::Exit
            | CfgNodeKind::LoopHeader
            | CfgNodeKind::Declaration
            | CfgNodeKind::Log => {}
        }
        if complete {
            TransferOutcome::Known(output)
        } else {
            TransferOutcome::Opaque {
                provisional: output,
                reason: "unknown expression dependencies".into(),
            }
        }
    }
}

fn collect(
    analysis: &LivenessAnalysis<'_>,
    expression: ExprId,
    live: &mut BTreeSet<AccessKey>,
    variables: &BTreeMap<parser::hir::SymbolId, super::field::FieldValue>,
) -> bool {
    expression.visit_accesses(analysis.hir, &mut |path| {
        live.insert(key_for_path(analysis.hir, analysis.field, path, variables));
    })
}

impl Transfer<LivenessAnalysis<'_>, LiveState, String> for CfgEdge {
    fn apply(
        &self,
        analysis: &LivenessAnalysis<'_>,
        input: &LiveState,
    ) -> TransferOutcome<LiveState, String> {
        let Some(condition) = self.condition else {
            return TransferOutcome::Known(input.clone());
        };
        let Some(value) =
            eval_expression(analysis.hir, analysis.field, condition, &BTreeMap::new())
        else {
            return TransferOutcome::Known(input.clone());
        };
        let truth = !analysis.field.is_zero(&value);
        let taken = match self.kind {
            EdgeKind::True => truth,
            EdgeKind::False => !truth,
            EdgeKind::Normal | EdgeKind::Loop | EdgeKind::Return => true,
        };
        TransferOutcome::Known(if taken { input.clone() } else { LiveState::Unreachable })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use parser::hir::{lower_project, ExprKind};
    use parser::new_frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;
    use std::fs;

    #[test]
    fn production_liveness_domain_and_read_transfer_are_monotone() {
        let directory = std::env::temp_dir()
            .join(format!("circomspect-phase4-live-laws-{}", std::process::id()));
        fs::create_dir_all(&directory).unwrap();
        let source = directory.join("case.circom");
        fs::write(
            &source,
            "template T(){signal input x; signal input y; signal output z; z<==x+y;}",
        )
        .unwrap();
        let loaded =
            load_sources(&[source], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let hir = lower_project(&loaded).hir;
        let field = FieldContext::for_curve(Curve::Bn254);
        let paths: Vec<_> = hir
            .expressions()
            .iter()
            .filter_map(|expr| match &expr.kind {
                ExprKind::Access(path)
                    if hir
                        .symbol(path.root)
                        .is_some_and(|symbol| symbol.name == "x" || symbol.name == "y") =>
                {
                    Some(key_for_path(&hir, &field, path, &BTreeMap::new()))
                }
                _ => None,
            })
            .collect();
        assert_eq!(paths.len(), 2);
        let mut states = vec![LiveState::Unreachable];
        for mask in 0..4_u8 {
            let mut keys = BTreeSet::new();
            for (index, key) in paths.iter().enumerate() {
                if mask & (1 << index) != 0 {
                    keys.insert(key.clone());
                }
            }
            states.push(LiveState::Reached(keys));
        }
        for left in &states {
            for right in &states {
                let mut joined = left.clone();
                let changed = joined.join_assign(right);
                assert_eq!(changed, joined != *left);
                assert!(left.leq(&joined) && right.leq(&joined));
                let mut reverse = right.clone();
                reverse.join_assign(left);
                assert_eq!(joined, reverse);
            }
        }
        let expression = hir
            .expressions()
            .iter()
            .find_map(|expr| {
                let ExprKind::Binary { .. } = &expr.kind else { return None };
                Some(expr.id)
            })
            .unwrap();
        let node =
            CfgNode { id: NodeId::new(0), kind: CfgNodeKind::Evaluate(expression), origin: None };
        let analysis = LivenessAnalysis::new(&hir, &field, hir.definition("T").unwrap());
        for left in &states {
            for right in &states {
                if !left.leq(right) {
                    continue;
                }
                let TransferOutcome::Known(left_after) = node.apply(&analysis, left) else {
                    panic!("known read")
                };
                let TransferOutcome::Known(right_after) = node.apply(&analysis, right) else {
                    panic!("known read")
                };
                assert!(left_after.leq(&right_after));
            }
        }
    }
}
