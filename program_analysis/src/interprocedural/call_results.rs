//! Complete exact call results permitted to specialize one definition's local transfer.

use std::collections::BTreeSet;

use abstract_interpretation::graph::FlowGraph;
use parser::hir::{AccessPath, CallTarget, DefinitionRef, ExprId, ExprKind, FunctionId, SymbolKind};

use crate::scalar_evidence::ScalarExpressionEvidence;
use crate::hir_cfg::{build_cfg_with_exact_calls, CfgNodeKind, DefinitionCfg};
use crate::hir_facts::{AnalysisFacts, FieldValue, OwnedAnalysisOptions, Range};
use crate::hir_facts::analyze_owned_with_scalar_calls;
use crate::interprocedural::{CallContext, CallOwner, CallProvenance, CallSite, ProjectAnalysis};
use crate::interprocedural::SummaryBlocker;
use parser::hir::SymbolId;
use std::collections::BTreeMap;

enum Visit {
    Enter(FunctionId),
    Leave(FunctionId),
}

impl ProjectAnalysis<'_> {
    pub(super) fn with_refined_facts<T>(
        &self,
        context: &CallContext,
        parameters: &BTreeMap<SymbolId, FieldValue>,
        work: impl FnOnce(&DefinitionCfg, &AnalysisFacts<'_>) -> Result<T, SummaryBlocker>,
    ) -> Result<T, SummaryBlocker> {
        let facts = self.refined_facts(context, parameters, None)?;
        work(facts.cfg(), &facts)
    }

    pub(super) fn refined_facts<'a>(
        &'a self,
        context: &CallContext,
        parameters: &BTreeMap<SymbolId, FieldValue>,
        budget: Option<usize>,
    ) -> Result<AnalysisFacts<'a>, SummaryBlocker> {
        const MAX_REFINEMENTS: usize = 64;
        self.contexts().check_context(context)?;
        let definition = context.definition();
        let mut calls = ScalarExpressionEvidence::empty(self.hir(), context, self.curve().clone());
        for _ in 0..MAX_REFINEMENTS {
            let cfg = build_cfg_with_exact_calls(self.hir(), definition, &calls, parameters)
                .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
            let facts = analyze_owned_with_scalar_calls(
                self.hir(),
                cfg,
                self.field_context(),
                OwnedAnalysisOptions { values: parameters.clone(), calls: calls.clone(), budget },
            )
            .map_err(|error| SummaryBlocker::LocalAnalysis(format!("{error:?}")))?;
            let discovered = self.certified_scalar_evidence(context, &facts);
            let mut next = calls.clone();
            let changed =
                next.merge(&discovered).map_err(|()| SummaryBlocker::UnsupportedContext)?;
            if !changed {
                self.check_exact_assignment_shapes(facts.cfg(), &facts)?;
                return Ok(facts);
            }
            calls = next;
        }
        Err(SummaryBlocker::ContextBudget)
    }

    fn check_exact_assignment_shapes(
        &self,
        cfg: &DefinitionCfg,
        facts: &AnalysisFacts<'_>,
    ) -> Result<(), SummaryBlocker> {
        for id in cfg.nodes() {
            let Some(CfgNodeKind::OpaqueAssignment { target, value, .. }) =
                cfg.node(*id).map(|node| &node.kind)
            else {
                continue;
            };
            if facts.exact_call_value(*value).is_none() || !target.steps.is_empty() {
                continue;
            }
            let Some(symbol) = self.hir().symbol(target.terminal) else { continue };
            if symbol.rank == 0 && symbol.bus_type.is_none() {
                continue;
            }
            match facts.reachable_node(*id).certified() {
                Some(false) => {}
                Some(true) => return Err(SummaryBlocker::InvalidAssignment(*value)),
                None => return Err(SummaryBlocker::UnsupportedContext),
            }
        }
        Ok(())
    }

    pub(super) fn exact_site_context(
        &self,
        site: &CallSite,
        facts: &AnalysisFacts<'_>,
    ) -> Result<CallContext, SummaryBlocker> {
        let expression = self.checked_provisional_site(site, facts)?;
        Self::certified_refined_result(expression, facts)?;
        let Some(ExprKind::Call { target: CallTarget::Function(id), arguments }) =
            self.hir().expression(expression).map(|expr| &expr.kind)
        else {
            return Err(SummaryBlocker::UnsupportedCallForm);
        };
        if site.resolved() != Some(DefinitionRef::Function(*id)) {
            return Err(SummaryBlocker::ForeignCall);
        }
        let arguments = self.contexts().exact_call_arguments(arguments, facts)?;
        self.contexts().context_for(DefinitionRef::Function(*id), arguments)
    }

    fn checked_provisional_site(
        &self,
        site: &CallSite,
        facts: &AnalysisFacts<'_>,
    ) -> Result<ExprId, SummaryBlocker> {
        if site.provenance != CallProvenance::Provisional
            || self.graph().site(site.id()) != Some(site)
            || site.owner != CallOwner::Definition(facts.definition())
            || self.hir().identity() != facts.hir().identity()
            || self.curve() != facts.curve()
        {
            return Err(SummaryBlocker::ForeignCall);
        }
        site.expression.ok_or(SummaryBlocker::UnsupportedCallForm)
    }

    fn certified_refined_result(
        expression: ExprId,
        facts: &AnalysisFacts<'_>,
    ) -> Result<(), SummaryBlocker> {
        let reachable = facts.reachable_expression(expression);
        match reachable.into_result() {
            Ok(true) => {}
            Ok(false) => return Err(SummaryBlocker::ExternalSummary),
            Err(blockers) => return Err(SummaryBlocker::LocalFacts(blockers)),
        }
        if facts.exact_call_value(expression).is_none() {
            return Err(SummaryBlocker::ExternalSummary);
        }
        Ok(())
    }

    fn certified_scalar_evidence(
        &self,
        context: &CallContext,
        facts: &AnalysisFacts<'_>,
    ) -> ScalarExpressionEvidence {
        let definition = context.definition();
        let mut results =
            ScalarExpressionEvidence::empty(self.hir(), context, self.curve().clone());
        if !self.refined_scope_matches(context, facts) {
            return results;
        }
        let owner = CallOwner::Definition(definition);
        for site in self.graph().calls_from(owner) {
            self.record_certified_call(site, facts, &mut results);
        }
        for expression in self.hir().expressions() {
            self.record_certified_access(expression.id, facts, &mut results);
        }
        results
    }

    fn refined_scope_matches(&self, context: &CallContext, facts: &AnalysisFacts<'_>) -> bool {
        facts.definition() == context.definition()
            && self.hir().identity() == facts.hir().identity()
            && self.curve() == facts.curve()
            && facts.refined_context() == Some(context)
    }

    fn record_certified_call(
        &self,
        site: &CallSite,
        facts: &AnalysisFacts<'_>,
        results: &mut ScalarExpressionEvidence,
    ) {
        let Some((expression, callee, arguments)) = self.checked_call_site(site, facts) else {
            return;
        };
        let Some((value, dependencies, callee_context)) =
            self.complete_exact_value(callee, arguments, facts)
        else {
            return;
        };
        results.insert_call(expression, value, dependencies);
        if self.call_is_removable(callee, &callee_context, arguments, facts) {
            results.certify_removable_call(expression);
        }
    }

    fn record_certified_access(
        &self,
        expression: ExprId,
        facts: &AnalysisFacts<'_>,
        results: &mut ScalarExpressionEvidence,
    ) {
        let Some(ExprKind::Access(path)) = self.hir().expression(expression).map(|item| &item.kind)
        else {
            return;
        };
        if !path.steps.is_empty() {
            return;
        }
        let fact = facts.range(expression);
        let Some(Range::Exact(value)) = fact.certified() else { return };
        results.insert_access(expression, value.clone());
    }

    fn checked_call_site<'a>(
        &'a self,
        site: &CallSite,
        facts: &AnalysisFacts<'_>,
    ) -> Option<(ExprId, FunctionId, &'a [ExprId])> {
        if site.provenance == CallProvenance::Unattached {
            return None;
        }
        let DefinitionRef::Function(callee) = site.resolved()? else { return None };
        if !self.acyclic_function_calls(callee) {
            return None;
        }
        let expression = site.expression?;
        if facts.reachable_expression(expression).certified() != Some(&true) {
            return None;
        }
        let ExprKind::Call { target: CallTarget::Function(id), arguments } =
            &self.hir().expression(expression)?.kind
        else {
            return None;
        };
        (*id == callee).then_some((expression, callee, arguments.as_slice()))
    }

    fn complete_exact_value(
        &self,
        callee: FunctionId,
        arguments: &[ExprId],
        facts: &AnalysisFacts<'_>,
    ) -> Option<(FieldValue, BTreeSet<usize>, CallContext)> {
        let definition = DefinitionRef::Function(callee);
        self.sources().validated_header(definition).ok()?;
        if self.sources().definition_has_hard_source_issue(definition).ok()? {
            return None;
        }
        let arguments = self.contexts().exact_call_arguments(arguments, facts).ok()?;
        let context = self.contexts().context_for(definition, arguments).ok()?;
        let summary = self.function(callee, &context);
        let item = summary.certified()?;
        let Range::Exact(value) = item.complete_return()? else { return None };
        Some((value.clone(), item.input_dependencies().clone(), context))
    }

    fn call_is_removable(
        &self,
        callee: FunctionId,
        context: &CallContext,
        arguments: &[ExprId],
        facts: &AnalysisFacts<'_>,
    ) -> bool {
        if self
            .with_local_function(callee, context, |_, _, facts| {
                self.sources().validated_definition(facts).map(|_| ())
            })
            .is_err()
        {
            return false;
        }
        let effects = self.function_effects(callee, context);
        let Some(effects) = effects.certified() else { return false };
        if !effects.is_empty() {
            return false;
        }
        for argument in arguments {
            if !self.removable_argument(*argument, facts) {
                return false;
            }
        }
        true
    }

    fn removable_argument(&self, id: ExprId, facts: &AnalysisFacts<'_>) -> bool {
        let Some(expression) = self.hir().expression(id) else { return false };
        match &expression.kind {
            ExprKind::Number(_) => true,
            ExprKind::Access(path) => {
                self.safe_local_scalar_read(path) || facts.safe_scalar_evaluation(id)
            }
            ExprKind::Call { .. } => facts.removable_call(id),
            ExprKind::Unary { .. } | ExprKind::Binary { .. } => facts.safe_scalar_evaluation(id),
            ExprKind::Array(_)
            | ExprKind::Tuple(_)
            | ExprKind::AnonymousComponent { .. }
            | ExprKind::Ternary { .. }
            | ExprKind::Parallel(_)
            | ExprKind::Opaque(_) => false,
        }
    }

    fn safe_local_scalar_read(&self, path: &AccessPath) -> bool {
        if !path.steps.is_empty() || path.component_input || path.component_output {
            return false;
        }
        let Some(symbol) = self.hir().symbol(path.root) else { return false };
        symbol.kind == SymbolKind::Variable && symbol.rank == 0
    }

    fn acyclic_function_calls(&self, start: FunctionId) -> bool {
        let mut stack = vec![Visit::Enter(start)];
        let mut active = BTreeSet::new();
        let mut done = BTreeSet::new();
        while let Some(visit) = stack.pop() {
            match visit {
                Visit::Enter(id) => {
                    if !self.enter_function(id, &mut active, &done, &mut stack) {
                        return false;
                    }
                }
                Visit::Leave(id) => {
                    active.remove(&id);
                    done.insert(id);
                }
            }
        }
        true
    }

    fn enter_function(
        &self,
        id: FunctionId,
        active: &mut BTreeSet<FunctionId>,
        done: &BTreeSet<FunctionId>,
        stack: &mut Vec<Visit>,
    ) -> bool {
        const MAX_FUNCTIONS: usize = 64;
        if done.contains(&id) {
            return true;
        }
        if active.contains(&id) || active.len() + done.len() >= MAX_FUNCTIONS {
            return false;
        }
        active.insert(id);
        stack.push(Visit::Leave(id));
        let owner = CallOwner::Definition(DefinitionRef::Function(id));
        for site in self.graph().calls_from(owner) {
            if let Some(DefinitionRef::Function(callee)) = site.resolved() {
                stack.push(Visit::Enter(callee));
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use std::fs;

    use parser::hir::{lift_project, DefinitionRef};
    use parser::frontend::{load_sources, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::build_cfg;
    use crate::hir_facts::{FieldContext, Range};
    use crate::interprocedural::{
        ArgumentValue, CallOwner, CallReachability, ProjectAnalysis, SummaryBlocker,
    };
    use crate::rules::{run_registered, RuleContext, RuleKind};

    fn fixture(source: &str, name: &str) -> parser::hir::LiftedProject {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-refined-site-{}-{name}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("case.circom");
        fs::write(&path, source).unwrap();
        let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        lift_project(&loaded)
    }

    #[test]
    fn cloned_site_with_mutated_source_span_cannot_authorize_exact_context() {
        let source = "function F(){return 7;} template T(){var x=F();}";
        let lifted = fixture(source, "mutated-span");
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let parent = lifted.hir.definition("T").unwrap();
        let caller = provider.contexts().symbolic_root(parent).unwrap();
        let cfg = build_cfg(&lifted.hir, parent).unwrap();
        let facts = provider.contexts().analyze_for_evidence(&cfg, &caller, None).unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(parent))[0];
        assert!(provider.exact_site_context(site, &facts).is_ok());
        let mut forged = site.clone();
        let DefinitionRef::Function(id) = lifted.hir.definition("F").unwrap() else {
            panic!("F must be a function")
        };
        forged.span = lifted.hir.function(id).unwrap().name_span;
        assert_eq!(provider.exact_site_context(&forged, &facts), Err(SummaryBlocker::ForeignCall));
    }

    #[test]
    fn exact_return_without_effect_freedom_keeps_value_but_not_removal_proof() {
        let lifted = fixture(
            "function Noisy(){log(1);return 7;}function Check(){var y=Noisy();return 7;}",
            "impure-return",
        );
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("Check").unwrap();
        let evidence = provider.contexts().symbolic_root(definition).unwrap();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
        let expression = site.expression.unwrap();
        let exact = FieldContext::for_curve(Curve::Bn254).canonical(7.into());
        assert_eq!(facts.exact_call_value(expression), Some(&exact));
        assert_eq!(facts.range(expression).certified(), Some(&Range::Exact(exact)));
        assert!(!facts.removable_call(expression));
    }

    #[test]
    fn removal_proof_cannot_cross_context_curve_or_project() {
        let source = concat!(
            "function Pure(n){return n;}",
            "template Check(n){var x=n;var y=Pure(x);}",
            "component main=Check(1);"
        );
        let lifted = fixture(source, "bound-proof");
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("Check").unwrap();
        let main = provider.graph().calls_from(CallOwner::Main(0))[0];
        let CallReachability::Reachable(call) =
            provider.graph().reachable_main_call(main.id(), &lifted.hir)
        else {
            panic!("main call must be reachable")
        };
        let evidence = provider.contexts().main_evidence(&call).unwrap();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
        let expression = site.expression.unwrap();
        assert!(facts.removable_call(expression));

        let field = FieldContext::for_curve(Curve::Bn254);
        let sibling = provider
            .contexts()
            .context_for(definition, vec![ArgumentValue::Scalar(field.canonical(2.into()))])
            .unwrap();
        assert!(!provider.certified_scalar_evidence(&sibling, &facts).removable_call(expression));
        let other_curve = ProjectAnalysis::build(&lifted, Curve::Goldilocks).unwrap();
        let curve_context = other_curve
            .contexts()
            .context_for(
                definition,
                vec![ArgumentValue::Scalar(
                    FieldContext::for_curve(Curve::Goldilocks).canonical(1.into()),
                )],
            )
            .unwrap();
        assert!(!other_curve
            .certified_scalar_evidence(&curve_context, &facts)
            .removable_call(expression));
        let other_project = fixture(source, "foreign-proof");
        let foreign = ProjectAnalysis::build(&other_project, Curve::Bn254).unwrap();
        let foreign_definition = other_project.hir.definition("Check").unwrap();
        let foreign_context = foreign
            .contexts()
            .context_for(foreign_definition, vec![ArgumentValue::Scalar(field.canonical(1.into()))])
            .unwrap();
        assert!(!foreign
            .certified_scalar_evidence(&foreign_context, &facts)
            .removable_call(expression));
    }

    #[test]
    fn invalid_callee_source_cannot_supply_exact_value_to_numeric_rule() {
        for (source, name) in [
            (
                "function Bad(n,n){return 0-1;}template Check(){var y=Bad(1,2)<0;}",
                "duplicate-parameter",
            ),
            (
                "function Bad(){return 0-1;var x=Missing();}\
                 template Check(){var y=Bad()<0;}",
                "missing-in-dead-callee",
            ),
        ] {
            let lifted = fixture(source, name);
            let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
            let definition = lifted.hir.definition("Check").unwrap();
            let evidence = provider.contexts().symbolic_root(definition).unwrap();
            let cfg = build_cfg(&lifted.hir, definition).unwrap();
            let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
            let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
            let expression = site.expression.unwrap();
            let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
            let result = run_registered(&context).unwrap();
            assert!(
                !result
                    .findings()
                    .iter()
                    .any(|finding| finding.kind() == RuleKind::FieldComparison),
                "{name}"
            );
            assert!(facts.exact_call_value(expression).is_none(), "{name}");
        }
    }

    #[test]
    fn unrelated_invalid_definition_does_not_hide_a_valid_exact_call() {
        let lifted = fixture(
            "function Broken(n,n){return 7;}function Good(){return 7;}\
             template Check(){var y=Good();}",
            "unrelated-invalid-definition",
        );
        let provider = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let definition = lifted.hir.definition("Check").unwrap();
        let evidence = provider.contexts().symbolic_root(definition).unwrap();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let site = provider.graph().calls_from(CallOwner::Definition(definition))[0];
        let expression = site.expression.unwrap();
        let expected = FieldContext::for_curve(Curve::Bn254).canonical(7.into());
        assert_eq!(facts.exact_call_value(expression), Some(&expected));
    }
}
