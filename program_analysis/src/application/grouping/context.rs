use abstract_interpretation::graph::FlowGraph;
use parser::frontend::{AssignmentOperator, Span};
use parser::hir::{DefinitionRef, ExprId, ExprKind, HirProject, SymbolId, SymbolKind};

use crate::hir_cfg::{CfgNodeKind, DefinitionCfg};
use crate::hir_facts::VisitAccesses;
use crate::interprocedural::{ArgumentValue, CallContext, ContextEvidence};
use crate::rules::{Finding, RuleKind};

#[derive(Clone)]
pub(crate) enum ContextDisplay {
    Omit,
    Qualify { context: CallContext, span: Span, message: String },
}

impl ContextDisplay {
    pub(crate) fn for_finding(
        finding: &Finding,
        cfg: &DefinitionCfg,
        hir: &HirProject,
        evidence: &ContextEvidence,
    ) -> Self {
        if evidence.call_path().is_empty() || evidence.context().arguments().is_empty() {
            return Self::Omit;
        }
        match finding.kind() {
            RuleKind::BitwiseComplement
            | RuleKind::Bn254SpecificCircuit
            | RuleKind::TooManyArguments => return Self::Omit,
            RuleKind::UnusedVariableValue | RuleKind::SideEffectFreeAssignment => {
                if let Some((target, statement, value)) =
                    assignment(finding.primary_span(), cfg, hir)
                {
                    let source_local =
                        finding.kind() == RuleKind::UnusedVariableValue || closed_value(value, hir);
                    if source_local && !later_read(target, statement, cfg, hir) {
                        return Self::Omit;
                    }
                }
            }
            RuleKind::ConstantConditional
            | RuleKind::FieldArithmetic
            | RuleKind::FieldComparison
            | RuleKind::NonstrictBinaryConversion
            | RuleKind::UnconstrainedDivision
            | RuleKind::SignalAssignment
            | RuleKind::RedundantWitnessAssignment
            | RuleKind::UnconstrainedSignal
            | RuleKind::UnconstrainedLessThan
            | RuleKind::UnusedParameterValue
            | RuleKind::UnusedOutputSignal
            | RuleKind::Complexity
            | RuleKind::IncompleteCoverage => {}
        }
        Self::for_evidence(hir, evidence)
    }

    pub(crate) fn for_evidence(hir: &HirProject, evidence: &ContextEvidence) -> Self {
        let Some(site) = evidence.call_path().last() else { return Self::Omit };
        let (name, parameters) = match evidence.context().definition() {
            DefinitionRef::Function(id) => {
                let Some(item) = hir.function(id) else { return Self::Omit };
                (&item.name, &item.parameters)
            }
            DefinitionRef::Template(id) => {
                let Some(item) = hir.template(id) else { return Self::Omit };
                (&item.name, &item.parameters)
            }
            DefinitionRef::Bus(id) => {
                let Some(item) = hir.bus(id) else { return Self::Omit };
                (&item.name, &item.parameters)
            }
        };
        if parameters.is_empty() {
            return Self::Omit;
        }
        let mut bindings = Vec::new();
        for (parameter, argument) in parameters.iter().zip(evidence.context().arguments()) {
            let Some(symbol) = hir.symbol(*parameter) else { return Self::Omit };
            let value = match argument {
                ArgumentValue::Scalar(value) => value.as_bigint().to_string(),
                ArgumentValue::Array(values) => format!("array of {} elements", values.len()),
                ArgumentValue::Bus(fields) => format!("bus with {} fields", fields.len()),
                ArgumentValue::Symbolic(_) => "symbolic".into(),
            };
            bindings.push(format!("{} = {value}", symbol.name));
        }
        Self::Qualify {
            context: evidence.context().clone(),
            span: site.span(),
            message: format!("Observed for {name}({}).", bindings.join(", ")),
        }
    }
}

fn assignment(
    span: Span,
    cfg: &DefinitionCfg,
    hir: &HirProject,
) -> Option<(SymbolId, Span, ExprId)> {
    for id in cfg.nodes() {
        let node = cfg.node(*id)?;
        let (CfgNodeKind::Assignment { target, value, operator }
        | CfgNodeKind::DeferredAssignment { target, value, operator }) = &node.kind
        else {
            continue;
        };
        let statement = node.origin?.span;
        if (target.span != span && statement != span) || !target.steps.is_empty() {
            continue;
        }
        if *operator != AssignmentOperator::Assign {
            return None;
        }
        let symbol = hir.symbol(target.root)?;
        if symbol.kind != SymbolKind::Variable || symbol.rank != 0 || symbol.bus_type.is_some() {
            return None;
        }
        return Some((target.root, statement, *value));
    }
    None
}

// Source order guides explanation relevance; it does not prove universal deadness.
// The original CFG retains reads erased by specialization, including zero-iteration loops.
fn later_read(target: SymbolId, statement: Span, cfg: &DefinitionCfg, hir: &HirProject) -> bool {
    for expression in cfg.evaluated_expressions() {
        let Some(expression) = hir.expression(expression) else { return true };
        if !after(expression.span, statement) {
            continue;
        }
        if let ExprKind::Access(path) = &expression.kind {
            if path.root == target {
                return true;
            }
        }
        if let ExprKind::Opaque(_) = &expression.kind {
            return true;
        }
    }
    for id in cfg.nodes() {
        let Some(node) = cfg.node(*id) else { return true };
        if implicit_read(target, statement, node, hir) {
            return true;
        }
    }
    false
}

fn implicit_read(
    target: SymbolId,
    statement: Span,
    node: &crate::hir_cfg::CfgNode,
    hir: &HirProject,
) -> bool {
    if let CfgNodeKind::Branch { condition, .. } = &node.kind {
        let mut reads = false;
        let complete = condition.visit_accesses(hir, &mut |path| reads |= path.root == target);
        return reads || !complete;
    }
    if !node.origin.is_some_and(|origin| after(origin.span, statement)) {
        return false;
    }
    if let CfgNodeKind::Update { target: path, .. } = &node.kind {
        return path.root == target;
    }
    if let CfgNodeKind::Assignment { target: path, operator, .. }
    | CfgNodeKind::DeferredAssignment { target: path, operator, .. } = &node.kind
    {
        return path.root == target && *operator != AssignmentOperator::Assign;
    }
    if let CfgNodeKind::OpaqueAssignment { target: path, value, operator, .. } = &node.kind {
        let mut reads = path.root == target && *operator != AssignmentOperator::Assign;
        let complete = value.visit_accesses(hir, &mut |path| reads |= path.root == target);
        return reads || !complete;
    }
    if let CfgNodeKind::Opaque(_) = &node.kind {
        return true;
    }
    false
}

fn closed_value(value: ExprId, hir: &HirProject) -> bool {
    let mut reads = false;
    let complete = value.visit_accesses(hir, &mut |_| reads = true);
    complete && !reads
}

fn after(span: Span, statement: Span) -> bool {
    span.source() == statement.source() && span.start() >= statement.end()
}

#[cfg(test)]
mod tests {
    use abstract_interpretation::graph::FlowGraph;
    use parser::hir::lift_project;

    use crate::application::grouping::context::later_read;
    use crate::application::grouping::tests::loaded;
    use crate::hir_cfg::{build_cfg, CfgNodeKind};

    #[test]
    fn incomplete_branch_reads_keep_context_qualification() {
        let project = lift_project(&loaded("template Root(n){var x=1;if(Missing()){log(0);}}"));
        let cfg = build_cfg(&project.hir, project.hir.definition("Root").unwrap()).unwrap();
        let (target, span) = cfg
            .nodes()
            .iter()
            .find_map(|id| {
                let node = cfg.node(*id)?;
                let CfgNodeKind::Assignment { target, .. } = &node.kind else { return None };
                Some((target.root, node.origin?.span))
            })
            .unwrap();
        assert!(later_read(target, span, &cfg, &project.hir));
    }
}
