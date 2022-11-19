use log::debug;

use program_structure::cfg::Cfg;
use program_structure::constants::Curve;
use program_structure::ir::{AssignOp, Expression, Meta, Statement};
use program_structure::report::{Report, ReportCollection};
use program_structure::report_code::ReportCode;
use program_structure::file_definition::{FileLocation, FileID};

const BN128_SPECIFIC_CIRCUITS: [&str; 12] = [
    "Sign",
    "AliasCheck",
    "CompConstant",
    "Num2Bits_strict",
    "Bits2Num_strict",
    "Bits2Point_Strict",
    "Point2Bits_Strict",
    "SMTVerifier",
    "SMTProcessor",
    "EdDSAVerifier",
    "EdDSAPoseidonVerifier",
    "EdDSAMiMCSpongeVerifier",
];

pub struct BN128SpecificCircuitWarning {
    template_name: String,
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl BN128SpecificCircuitWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            format!(
                "The `{}` template hard-codes BN128 specific parameters and should not be used with other curves.",
                self.template_name
            ),
            ReportCode::BN128SpecificCircuit,
        );
        if let Some(file_id) = self.file_id {
            report.add_primary(
                self.file_location,
                file_id,
                format!("`{}` instantiated here.", self.template_name),
            );
        }
        report
    }
}

pub fn find_bn128_specific_circuits(cfg: &Cfg) -> ReportCollection {
    if cfg.constants().curve() == &Curve::Bn128 {
        // Exit early if we're using the default curve.
        return ReportCollection::new();
    }
    debug!("running bn128-specific circuits analysis pass");
    let mut reports = ReportCollection::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            visit_statement(stmt, &mut reports);
        }
    }
    debug!("{} new reports generated", reports.len());
    reports
}

fn visit_statement(stmt: &Statement, reports: &mut ReportCollection) {
    use AssignOp::*;
    use Expression::*;
    use Statement::*;
    if let Substitution { meta: var_meta, op: AssignLocalOrComponent, rhe, .. } = stmt {
        // If the variable `var` is declared as a local variable or signal, we exit early.
        if var_meta.type_knowledge().is_local() || var_meta.type_knowledge().is_signal() {
            return;
        }
        // If this is an update node, we extract the right-hand side.
        let rhe = if let Update { rhe, .. } = rhe { rhe } else { rhe };

        // A component initialization on the form `var = component_name(...)`.
        if let Call { meta: component_meta, name: component_name, .. } = rhe {
            if BN128_SPECIFIC_CIRCUITS.contains(&&component_name[..]) {
                reports.push(build_report(component_meta, component_name));
            }
        }
    }
}

fn build_report(meta: &Meta, name: &str) -> Report {
    BN128SpecificCircuitWarning {
        template_name: name.to_string(),
        file_id: meta.file_id,
        file_location: meta.file_location(),
    }
    .into_report()
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::{cfg::IntoCfg, constants::Curve};

    use super::*;

    #[test]
    fn test_num2bits_strict() {
        let src = r#"
            template T(n) {
                signal input in;
                signal output out[n];

                component n2b = Num2Bits_strict(n);
                n2b.in === in;
                for (var i = 0; i < n; i++) {
                    out[i] <== n2b.out[i];
                }
            }
        "#;
        validate_reports(src, 1);

        let src = r#"
            template T(n) {
                signal input in;
                signal output out[n];

                component n2b = Num2Bits(n);
                n2b.in === in;
                for (var i = 0; i < n; i++) {
                    out[i] <== n2b.out[i];
                }
            }
        "#;
        validate_reports(src, 0);
    }

    fn validate_reports(src: &str, expected_len: usize) {
        // Build CFG.
        let mut reports = ReportCollection::new();
        let cfg = parse_definition(src)
            .unwrap()
            .into_cfg(&Curve::Goldilocks, &mut reports)
            .unwrap()
            .into_ssa()
            .unwrap();
        assert!(reports.is_empty());

        // Generate report collection.
        let reports = find_bn128_specific_circuits(&cfg);

        assert_eq!(reports.len(), expected_len);
    }
}
