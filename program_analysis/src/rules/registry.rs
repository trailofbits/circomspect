use std::collections::BTreeSet;

use crate::rules::{constraints, maintainability, numeric, uses, RuleContext, RuleKind, RuleResult};

/// A rule consumes one validated definition and call scope at a time.
pub trait Rule: Sync {
    fn kind(&self) -> RuleKind;
    fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult;
}

/// Registry order is fixed by the four independently owned rule families.
pub fn registered_rules() -> impl Iterator<Item = &'static dyn Rule> {
    [numeric::rules(), constraints::rules(), uses::rules(), maintainability::rules()]
        .into_iter()
        .flatten()
        .copied()
}

/// Run every implemented rule and reject findings outside its validated scope.
///
/// # Errors
/// Returns an error for duplicate rules or results with a foreign rule kind or call scope.
pub fn run_registered(context: &RuleContext<'_, '_, '_>) -> Result<RuleResult, RuleRunError> {
    run_rules(context, registered_rules())
}

fn run_rules<'a>(
    context: &RuleContext<'_, '_, '_>,
    rules: impl IntoIterator<Item = &'a dyn Rule>,
) -> Result<RuleResult, RuleRunError> {
    let mut seen = BTreeSet::new();
    let mut combined = RuleResult::default();
    for rule in rules {
        let kind = rule.kind();
        if !seen.insert(kind) {
            return Err(RuleRunError::DuplicateRule(kind));
        }
        let result = rule.run(context);
        for finding in result.findings() {
            if finding.kind() != kind {
                return Err(RuleRunError::WrongKind { expected: kind, actual: finding.kind() });
            }
            if finding.context() != context.call_context() {
                return Err(RuleRunError::ForeignFinding(kind));
            }
        }
        for abstention in result.abstentions() {
            if abstention.kind != kind {
                return Err(RuleRunError::WrongAbstentionKind {
                    expected: kind,
                    actual: abstention.kind,
                });
            }
            if &abstention.context != context.call_context() {
                return Err(RuleRunError::ForeignAbstention(kind));
            }
        }
        combined.append(result);
    }
    combined.sort();
    Ok(combined)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, thiserror::Error)]
pub enum RuleRunError {
    #[error("rule {0:?} appears more than once in the registry")]
    DuplicateRule(RuleKind),
    #[error("rule {expected:?} emitted a finding for {actual:?}")]
    WrongKind { expected: RuleKind, actual: RuleKind },
    #[error("rule {expected:?} abstained for {actual:?}")]
    WrongAbstentionKind { expected: RuleKind, actual: RuleKind },
    #[error("rule {0:?} emitted a finding for another call context")]
    ForeignFinding(RuleKind),
    #[error("rule {0:?} recorded an abstention for another call context")]
    ForeignAbstention(RuleKind),
}

#[cfg(test)]
mod tests {
    use std::fs;

    use parser::hir::{lift_project, DefinitionRef};
    use parser::frontend::{load_sources, Span, Version, VersionPolicy};
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::build_cfg;
    use crate::hir_facts::FieldContext;
    use crate::interprocedural::{ArgumentValue, ProjectAnalysis};

    use crate::rules::registry::{run_rules, Rule, RuleRunError};
    use crate::rules::{AbstentionReason, Finding, RuleContext, RuleKind, RuleResult, ScopedAbstention};

    struct Emits {
        kind: RuleKind,
        reported: RuleKind,
        abstain: bool,
    }

    impl Rule for Emits {
        fn kind(&self) -> RuleKind {
            self.kind
        }

        fn run(&self, context: &RuleContext<'_, '_, '_>) -> RuleResult {
            let DefinitionRef::Template(id) = context.call_context().definition() else {
                panic!("test fixture uses a template")
            };
            let span = context.hir().template(id).unwrap().name_span;
            let mut result = RuleResult::default();
            result.add_finding(context.finding(
                self.reported,
                "proved property".to_string(),
                span,
                "evidence".to_string(),
            ));
            if self.abstain {
                result.add_abstention(ScopedAbstention {
                    kind: self.kind,
                    context: context.call_context().clone(),
                    span,
                    reason: AbstentionReason::UnsupportedConstruct,
                });
            }
            result
        }
    }

    struct Returns {
        finding: Option<Finding>,
        abstention: Option<ScopedAbstention>,
    }

    impl Rule for Returns {
        fn kind(&self) -> RuleKind {
            RuleKind::Complexity
        }

        fn run(&self, _context: &RuleContext<'_, '_, '_>) -> RuleResult {
            let mut result = RuleResult::default();
            if let Some(finding) = &self.finding {
                result.add_finding(finding.clone());
            }
            if let Some(abstention) = &self.abstention {
                result.add_abstention(abstention.clone());
            }
            result
        }
    }

    fn with_context(test: impl FnOnce(&RuleContext<'_, '_, '_>, &ProjectAnalysis<'_>, Span)) {
        let directory = std::env::temp_dir().join(format!(
            "circomspect-rule-registry-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("case.circom");
        fs::write(&path, "template Check(n) {}\n").unwrap();
        let loaded = load_sources(&[path], &[directory], VersionPolicy::new(Version::new(2, 2, 3)));
        let lifted = lift_project(&loaded);
        let definition = lifted.hir.definition("Check").unwrap();
        let cfg = build_cfg(&lifted.hir, definition).unwrap();
        let summaries = ProjectAnalysis::build(&lifted, Curve::Bn254).unwrap();
        let evidence = summaries.contexts().symbolic_root(definition).unwrap();
        let facts = summaries.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let context = RuleContext::new(&facts, &summaries, &evidence).unwrap();
        let DefinitionRef::Template(id) = definition else { panic!("template definition") };
        test(&context, &summaries, lifted.hir.template(id).unwrap().name_span);
    }

    #[test]
    fn registry_sorts_findings_and_preserves_independent_local_result() {
        with_context(|context, _, _| {
            let later = Emits {
                kind: RuleKind::TooManyArguments,
                reported: RuleKind::TooManyArguments,
                abstain: true,
            };
            let earlier = Emits {
                kind: RuleKind::Complexity,
                reported: RuleKind::Complexity,
                abstain: false,
            };
            let result = run_rules(context, [&later as &dyn Rule, &earlier]).unwrap();
            assert_eq!(result.findings().len(), 2);
            assert_eq!(result.findings()[0].kind(), RuleKind::Complexity);
            assert_eq!(result.findings()[1].kind(), RuleKind::TooManyArguments);
            assert_eq!(result.abstentions().len(), 1);
        });
    }

    #[test]
    fn registry_rejects_wrong_kind_and_duplicates() {
        with_context(|context, _, span| {
            let wrong = Emits {
                kind: RuleKind::Complexity,
                reported: RuleKind::TooManyArguments,
                abstain: false,
            };
            assert_eq!(
                run_rules(context, [&wrong as &dyn Rule]).err(),
                Some(RuleRunError::WrongKind {
                    expected: RuleKind::Complexity,
                    actual: RuleKind::TooManyArguments,
                })
            );
            let correct = Emits {
                kind: RuleKind::Complexity,
                reported: RuleKind::Complexity,
                abstain: false,
            };
            assert_eq!(
                run_rules(context, [&correct as &dyn Rule, &correct]).err(),
                Some(RuleRunError::DuplicateRule(RuleKind::Complexity))
            );
            let wrong_abstention = Returns {
                finding: None,
                abstention: Some(ScopedAbstention {
                    kind: RuleKind::TooManyArguments,
                    context: context.call_context().clone(),
                    span,
                    reason: AbstentionReason::UnsupportedConstruct,
                }),
            };
            assert_eq!(
                run_rules(context, [&wrong_abstention as &dyn Rule]).err(),
                Some(RuleRunError::WrongAbstentionKind {
                    expected: RuleKind::Complexity,
                    actual: RuleKind::TooManyArguments,
                })
            );
        });
    }

    #[test]
    fn registry_rejects_results_from_another_project() {
        with_context(|foreign, _, span| {
            let finding = foreign.finding(
                RuleKind::Complexity,
                "proved".to_string(),
                span,
                "evidence".to_string(),
            );
            let abstention = ScopedAbstention {
                kind: RuleKind::Complexity,
                context: foreign.call_context().clone(),
                span,
                reason: AbstentionReason::UnsupportedConstruct,
            };
            with_context(|local, _, _| {
                let wrong_finding = Returns { finding: Some(finding), abstention: None };
                assert_eq!(
                    run_rules(local, [&wrong_finding as &dyn Rule]).err(),
                    Some(RuleRunError::ForeignFinding(RuleKind::Complexity))
                );
                let wrong_abstention = Returns { finding: None, abstention: Some(abstention) };
                assert_eq!(
                    run_rules(local, [&wrong_abstention as &dyn Rule]).err(),
                    Some(RuleRunError::ForeignAbstention(RuleKind::Complexity))
                );
            });
        });
    }

    #[test]
    fn registry_rejects_abstention_for_hypothetical_sibling_context() {
        with_context(|context, summaries, span| {
            let DefinitionRef::Template(definition) = context.call_context().definition() else {
                panic!("template definition")
            };
            let field = FieldContext::for_curve(Curve::Bn254);
            let hypothetical = summaries
                .contexts()
                .context_for(
                    DefinitionRef::Template(definition),
                    vec![ArgumentValue::Scalar(field.canonical(2.into()))],
                )
                .unwrap();
            assert!(summaries.contexts().check_context(&hypothetical).is_ok());
            assert_ne!(&hypothetical, context.call_context());
            let rule = Returns {
                finding: None,
                abstention: Some(ScopedAbstention {
                    kind: RuleKind::Complexity,
                    context: hypothetical,
                    span,
                    reason: AbstentionReason::SymbolicParameters,
                }),
            };
            assert_eq!(
                run_rules(context, [&rule as &dyn Rule]).err(),
                Some(RuleRunError::ForeignAbstention(RuleKind::Complexity))
            );
        });
    }
}
