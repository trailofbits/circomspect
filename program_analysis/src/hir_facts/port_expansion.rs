//! Ordered handles for a bounded rank-one port; callers retain role and warning policy.

use parser::hir::Port;

use crate::hir_facts::{AccessHandle, AccessHandleError, AnalysisFacts};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RankOnePortError {
    InvalidShape(AccessHandleError),
    InvalidRank,
    WidthLimit,
    InvalidHandle(AccessHandleError),
}

impl AnalysisFacts<'_> {
    /// Expand a selected port in index order after proving its shape and every handle.
    pub(crate) fn rank_one_port_handles(
        &self,
        port: &Port,
        max_width: usize,
    ) -> Result<Vec<AccessHandle>, RankOnePortError> {
        let dimensions =
            self.checked_symbol_dimensions(port.symbol).map_err(RankOnePortError::InvalidShape)?;
        let [width] = dimensions.as_slice() else { return Err(RankOnePortError::InvalidRank) };
        if *width == 0 || *width > max_width {
            return Err(RankOnePortError::WidthLimit);
        }
        let mut handles = Vec::with_capacity(*width);
        for index in 0..*width {
            let handle =
                self.port_handle(port.id, &[index]).map_err(RankOnePortError::InvalidHandle)?;
            handles.push(handle);
        }
        Ok(handles)
    }
}

#[cfg(test)]
mod tests {
    use parser::hir::DefinitionRef;
    use program_structure::utils::constants::Curve;

    use crate::hir_cfg::build_cfg;
    use crate::hir_facts::RankOnePortError;
    use crate::interprocedural::ProjectAnalysis;

    #[test]
    fn expansion_rejects_scalar_and_rank_two_ports_before_width_checks() {
        for shape in ["", "[2][3]", "[0][1]", "[513][1]"] {
            let project = crate::test_fixtures::port_project(shape);
            let provider = ProjectAnalysis::build(&project, Curve::Goldilocks).unwrap();
            let definition = project.hir.definition("T").unwrap();
            let evidence = provider.contexts().symbolic_root(definition).unwrap();
            let cfg = build_cfg(&project.hir, definition).unwrap();
            let facts = provider.contexts().analyze_for_evidence(&cfg, &evidence, None).unwrap();
            let DefinitionRef::Template(template) = definition else { panic!("template T") };
            let port = project.hir.template(template).unwrap().ports[1];
            let port = project.hir.port(port).unwrap();
            assert_eq!(
                facts.rank_one_port_handles(port, 512),
                Err(RankOnePortError::InvalidRank),
                "{shape}"
            );
        }
    }
}
