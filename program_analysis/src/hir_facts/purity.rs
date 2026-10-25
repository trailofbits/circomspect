//! Exact evaluation safety shared by backward demand and its reporting queries.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use abstract_interpretation::solver::SolveResult;
use parser::hir::{AccessPath, ExprId, ExprKind, HirProject, SymbolKind};

use crate::hir_cfg::{CfgNodeKind, DefinitionCfg};
use crate::hir_facts::forward::eval_expression_with_calls;
use crate::hir_facts::{AnalysisFacts, FieldContext, ForwardResult};
use crate::scalar_evidence::ScalarExpressionEvidence;

/// Proof that scalar evaluation is exact and removable at every live source site.
#[derive(Clone, Debug, Default)]
pub(super) struct ScalarEvaluationSafety {
    expressions: BTreeSet<ExprId>,
}

impl ScalarEvaluationSafety {
    pub(super) fn certify(
        hir: &HirProject,
        cfg: &DefinitionCfg,
        field: &FieldContext,
        forward: &ForwardResult,
        calls: Option<&ScalarExpressionEvidence>,
    ) -> Self {
        let SolveResult::Complete(facts) = forward else { return Self::default() };
        let mut expressions = BTreeSet::new();
        let mut unsafe_expressions = BTreeSet::new();
        for id in cfg.nodes() {
            let Some(CfgNodeKind::Evaluate(expression)) = cfg.node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            let Some(state) = facts.get(id).and_then(|facts| facts.input.as_ref()) else {
                unsafe_expressions.insert(*expression);
                continue;
            };
            let Some(variables) = state.variables() else { continue };
            if removable_structure(hir, *expression, calls)
                && eval_expression_with_calls(hir, field, *expression, variables, calls).is_some()
            {
                expressions.insert(*expression);
            } else {
                unsafe_expressions.insert(*expression);
            }
        }
        expressions.retain(|expression| !unsafe_expressions.contains(expression));
        Self { expressions }
    }

    pub(super) fn contains(&self, expression: ExprId) -> bool {
        self.expressions.contains(&expression)
    }
}

impl AnalysisFacts<'_> {
    /// Whether this definition proves exact, removable evaluation at every live site.
    pub(crate) fn safe_scalar_evaluation(&self, expression: ExprId) -> bool {
        self.scalar_evaluation_safety.contains(expression)
    }
}

fn removable_structure(
    hir: &HirProject,
    expression: ExprId,
    calls: Option<&ScalarExpressionEvidence>,
) -> bool {
    let Some(expression) = hir.expression(expression) else { return false };
    match &expression.kind {
        ExprKind::Number(_) => true,
        ExprKind::Access(path) => scalar_local_or_parameter(hir, path),
        ExprKind::Unary { operand, .. } => removable_structure(hir, *operand, calls),
        ExprKind::Binary { left, right, .. } => {
            removable_structure(hir, *left, calls) && removable_structure(hir, *right, calls)
        }
        ExprKind::Call { .. } => calls.is_some_and(|calls| calls.removable_call(expression.id)),
        ExprKind::Array(_)
        | ExprKind::Tuple(_)
        | ExprKind::AnonymousComponent { .. }
        | ExprKind::Ternary { .. }
        | ExprKind::Parallel(_)
        | ExprKind::Opaque(_) => false,
    }
}

fn scalar_local_or_parameter(hir: &HirProject, path: &AccessPath) -> bool {
    let Some(symbol) = hir.symbol(path.root) else { return false };
    (symbol.kind == SymbolKind::Variable || symbol.kind == SymbolKind::Parameter)
        && symbol.rank == 0
        && path.steps.is_empty()
        && !path.component_input
        && !path.component_output
}

#[cfg(test)]
mod tests {
    use abstract_interpretation::graph::FlowGraph;
    use abstract_interpretation::solver::SolveResult;
    use parser::hir::{lift_project, ExprKind};
    use parser::new_frontend::{load_sources, BinaryOperator, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::{build_cfg, CfgNodeKind};
    use crate::hir_facts::forward::ForwardState;
    use crate::interprocedural::ProjectSummaries;

    #[test]
    fn every_specialized_loop_site_must_have_safe_exact_evaluation() {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-purity-loop-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let path = directory.join("case.circom");
        std::fs::write(
            &path,
            "template Check(){signal input p;var a=1;\
             for(var i=0;i<2;i++){var x=a+1;a=p;}}",
        )
        .unwrap();
        let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let provider = ProjectSummaries::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("Check").unwrap();
        let evidence = provider.symbolic_root(definition).unwrap();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let SolveResult::Complete(_) = &facts.forward else {
            panic!("the loop safety regression needs complete forward facts")
        };
        let expression = lifted
            .hir
            .expressions()
            .iter()
            .find_map(|expression| {
                let ExprKind::Binary { operator: BinaryOperator::Add, .. } = &expression.kind
                else {
                    return None;
                };
                Some(expression.id)
            })
            .unwrap();
        let values: Vec<_> = facts
            .cfg()
            .nodes()
            .iter()
            .filter_map(|id| {
                let CfgNodeKind::Evaluate(evaluated) = facts.cfg().node(*id).unwrap().kind else {
                    return None;
                };
                if evaluated != expression {
                    return None;
                }
                let variables = facts.site_state(*id).and_then(ForwardState::variables).unwrap();
                Some(facts.evaluate(expression, variables))
            })
            .collect();
        assert_eq!(values.len(), 2, "the source expression must have two specialized evaluations");
        assert!(values[0].is_some());
        assert!(values[1].is_none());
        assert!(!facts.scalar_evaluation_safety.contains(expression));
    }
}
