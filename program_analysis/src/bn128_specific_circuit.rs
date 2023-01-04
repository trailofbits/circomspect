use log::debug;

use program_structure::cfg::Cfg;
use program_structure::constants::Curve;
use program_structure::ir::{AssignOp, Expression, Meta, Statement};
use program_structure::report::{Report, ReportCollection};
use program_structure::report_code::ReportCode;
use program_structure::file_definition::{FileLocation, FileID};

const PROBLEMATIC_GOLDILOCK_TEMPLATES: [&str; 23] = [
    "BabyPbk",
    "CompConstant",
    "EdDSAVerifier",
    "EdDSAMiMCVerifier",
    "EdDSAMiMCSpongeVerifier",
    "EdDSAPoseidonVerifier",
    "EscalarMulAny",
    "MiMC7",
    "MultiMiMC7",
    "MiMCFeistel",
    "MiMCSponge",
    "Pedersen",
    "Bits2Point_Strict",
    "Point2Bits_Strict",
    "PoseidonEx",
    "Poseidon",
    "Sign",
    "SMTHash1",
    "SMTHash2",
    "SMTProcessor",
    "SMTProcessorLevel",
    "SMTVerifier",
    "SMTVerifierLevel",
];

const PROBLEMATIC_BLS12_381_TEMPLATES: [&str; 13] = [
    "AliasCheck",
    "CompConstant",
    "Num2Bits_strict",
    "Bits2Num_strict",
    "EdDSAVerifier",
    "EdDSAMiMCVerifier",
    "EdDSAMiMCSpongeVerifier",
    "EdDSAPoseidonVerifier",
    "Bits2Point_Strict",
    "Point2Bits_Strict",
    "SMTVerifier",
    "SMTProcessor",
    "Sign",
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
                "The `{}` template relies on BN128 specific parameters and should not be used with other curves.",
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

// This analysis pass identifies Circomlib templates with hard-coded constants
// related to BN128. If these are used together with a different prime, this may
// be an issue.
//
// The following table contains a check for each problematic template-curve pair.
//
// Template             Goldilocks (64 bits)        BLS12-381 (255 bits)
// -----------------------------------------------------------------
// AliasCheck                                               x
// BabyPbk                      x
// Bits2Num_strict                                          x
// Num2Bits_strict                                          x
// CompConstant                 x                           x
// EdDSAVerifier                x                           x
// EdDSAMiMCVerifier            x                           x
// EdDSAMiMCSpongeVerifier      x                           x
// EdDSAPoseidonVerifier        x                           x
// EscalarMulAny                x
// MiMC7                        x
// MultiMiMC7                   x
// MiMCFeistel                  x
// MiMCSponge                   x
// Pedersen                     x
// Bits2Point_strict            x                           x
// Point2Bits_strict            x                           x
// PoseidonEx                   x
// Poseidon                     x
// Sign                         x                           x
// SMTHash1                     x
// SMTHash2                     x
// SMTProcessor                 x                           x
// SMTProcessorLevel            x
// SMTVerifier                  x                           x
// SMTVerifierLevel             x
pub fn find_bn128_specific_circuits(cfg: &Cfg) -> ReportCollection {
    let problematic_templates = match cfg.constants().curve() {
        Curve::Goldilocks => PROBLEMATIC_GOLDILOCK_TEMPLATES.to_vec(),
        Curve::Bls12_381 => PROBLEMATIC_BLS12_381_TEMPLATES.to_vec(),
        Curve::Bn128 => {
            // Exit early if we're using the default curve.
            return ReportCollection::new();
        }
    };
    debug!("running bn128-specific circuit analysis pass");
    let mut reports = ReportCollection::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            visit_statement(stmt, &problematic_templates, &mut reports);
        }
    }
    debug!("{} new reports generated", reports.len());
    reports
}

fn visit_statement(
    stmt: &Statement,
    problematic_templates: &[&str],
    reports: &mut ReportCollection,
) {
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
            if problematic_templates.contains(&&component_name[..]) {
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
            .into_cfg(&Curve::Bls12_381, &mut reports)
            .unwrap()
            .into_ssa()
            .unwrap();
        assert!(reports.is_empty());

        // Generate report collection.
        let reports = find_bn128_specific_circuits(&cfg);

        assert_eq!(reports.len(), expected_len);
    }
}
