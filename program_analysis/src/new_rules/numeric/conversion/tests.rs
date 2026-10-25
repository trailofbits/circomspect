use parser::hir::DefinitionRef;
use program_structure::utils::constants::Curve;

use crate::hir_cfg::build_cfg;
use crate::interprocedural::{ProjectSummaries, SummaryBlocker};

use crate::new_rules::{AbstentionReason, RuleContext};
use crate::new_rules::numeric::conversion::bit_handles;
use std::collections::BTreeSet;

#[test]
fn numeric_port_expansion_preserves_exact_boundaries_and_handle_order() {
    let cases = [
        ("[0]", Err(AbstentionReason::Summary(BTreeSet::from([SummaryBlocker::ContextBudget])))),
        ("[1]", Ok(1)),
        ("[512]", Ok(512)),
        ("[513]", Err(AbstentionReason::Summary(BTreeSet::from([SummaryBlocker::ContextBudget])))),
        ("[n]", Err(AbstentionReason::UnsupportedConstruct)),
    ];
    for (shape, expected) in cases {
        let project = crate::test_fixtures::port_project(shape);
        let provider = ProjectSummaries::build(&project, Curve::Goldilocks).unwrap();
        let definition = project.hir.definition("T").unwrap();
        let evidence = provider.symbolic_root(definition).unwrap();
        let cfg = build_cfg(&project.hir, definition).unwrap();
        let facts = provider.analyze_for_evidence(&cfg, &evidence, None).unwrap();
        let DefinitionRef::Template(template) = definition else { panic!("template T") };
        let ports = &project.hir.template(template).unwrap().ports;

        let context = RuleContext::new(&facts, &provider, &evidence).unwrap();
        let output = project.hir.port(ports[1]).unwrap();
        let result = bit_handles(&context, output);
        match expected {
            Ok(width) => {
                let handles = result.unwrap();
                assert_eq!(handles.len(), width);
                for (index, handle) in handles.iter().enumerate() {
                    assert_eq!(handle, &facts.port_handle(ports[1], &[index]).unwrap());
                }
            }
            Err(blocker) => assert_eq!(result.unwrap_err(), blocker, "{shape}"),
        }
    }
}
