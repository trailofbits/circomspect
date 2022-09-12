use log::debug;
use num_bigint::BigInt;

use program_structure::cfg::{Cfg, DefinitionType};
use program_structure::report_code::ReportCode;
use program_structure::report::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::value_meta::{ValueMeta, ValueReduction};
use program_structure::ir::*;

pub enum NonStrictBinaryConversionWarning {
    Num2Bits { file_id: Option<FileID>, location: FileLocation },
    Bits2Num { file_id: Option<FileID>, location: FileLocation },
}

impl NonStrictBinaryConversionWarning {
    pub fn into_report(self) -> Report {
        match self {
            NonStrictBinaryConversionWarning::Num2Bits { file_id, location } => {
                let mut report = Report::warning(
                    "Using `Num2Bits` to convert field elements to bits may lead to aliasing issues.".to_string(),
                    ReportCode::NonStrictBinaryConversion,
                );
                if let Some(file_id) = file_id {
                    report.add_primary(
                        location,
                        file_id,
                        "Circomlib template `Num2Bits` instantiated here.".to_string(),
                    );
                }
                report.add_note(
                    "Consider using `Num2Bits_strict` if the input may be 254 bits or larger."
                        .to_string(),
                );
                report
            }
            NonStrictBinaryConversionWarning::Bits2Num { file_id, location } => {
                let mut report = Report::warning(
                    "Using `Bits2Num` to convert arrays to field elements may lead to aliasing issues".to_string(),
                    ReportCode::NonStrictBinaryConversion,
                );
                if let Some(file_id) = file_id {
                    report.add_primary(
                        location,
                        file_id,
                        "Circomlib template `Bits2Num` instantiated here.".to_string(),
                    );
                }
                report.add_note(
                    "Consider using `Bits2Num_strict` if the input may be 254 bits or larger"
                        .to_string(),
                );
                report
            }
        }
    }
}

/// If the input `x` to the Circomlib circuit `NumBits` is 254 bits or greater
/// there will be two valid bit-representations of the input: One representation
/// of `x` and one of `p + x`. This is typically not expected by developers and
/// may lead to issues.
pub fn find_nonstrict_binary_conversion(cfg: &Cfg) -> ReportCollection {
    if matches!(cfg.definition_type(), DefinitionType::Function) {
        // Exit early if this is a function.
        return ReportCollection::new();
    }
    debug!("running non-strict `Num2Bits` analysis pass");
    let mut reports = ReportCollection::new();
    let prime_size = BigInt::from(cfg.constants().prime_size());
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            visit_statement(stmt, &prime_size, &mut reports);
        }
    }
    debug!("{} new reports generated", reports.len());
    reports
}

fn visit_statement(stmt: &Statement, prime_size: &BigInt, reports: &mut ReportCollection) {
    use AssignOp::*;
    use Expression::*;
    use Statement::*;
    use ValueReduction::*;
    // A component initialization on the form `var = component_name(args, ...)`.
    if let Substitution {
        meta: var_meta,
        op: AssignLocalOrComponent,
        rhe: Call { meta: component_meta, name: component_name, args },
        ..
    } = stmt
    {
        // If the variable `var` is declared as a local variable or signal, we exit early.
        if var_meta.type_knowledge().is_local() || var_meta.type_knowledge().is_signal() {
            return;
        }
        // We assume this is the `Num2Bits` circuit from Circomlib.
        if component_name == "Num2Bits" && args.len() == 1 {
            let arg = &args[0];
            // If the input size is known to be less than the prime size, this
            // initialization is safe.
            if let Some(FieldElement { value }) = arg.value() {
                if value < prime_size {
                    return;
                }
            }
            reports.push(build_num2bits(component_meta));
        }
        // We assume this is the `Bits2Num` circuit from Circomlib.
        if component_name == "Bits2Num" && args.len() == 1 {
            let arg = &args[0];
            // If the input size is known to be less than the prime size, this
            // initialization is safe.
            if let Some(FieldElement { value }) = arg.value() {
                if value < prime_size {
                    return;
                }
            }
            reports.push(build_bits2num(component_meta));
        }
    }
}

fn build_num2bits(meta: &Meta) -> Report {
    NonStrictBinaryConversionWarning::Num2Bits {
        file_id: meta.file_id(),
        location: meta.file_location(),
    }
    .into_report()
}

fn build_bits2num(meta: &Meta) -> Report {
    NonStrictBinaryConversionWarning::Bits2Num {
        file_id: meta.file_id(),
        location: meta.file_location(),
    }
    .into_report()
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::{cfg::IntoCfg, constants::Curve};

    use super::*;

    #[test]
    fn test_nonstrict_num2bits() {
        let src = r#"
            template F(n) {
                signal input in;
                signal output out[n];

                component n2b = Num2Bits(n);
                n2b.in === in;
                for (var i = 0; i < n; i++) {
                    out[i] <== n2b.out[i];
                }
            }
        "#;
        validate_reports(src, 1);

        let src = r#"
            template F(n) {
                signal input in;
                signal output out[n];

                var bits = 254;
                component n2b = Num2Bits(bits - 1);
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
            .into_cfg(&Curve::Bn128, &mut reports)
            .unwrap()
            .into_ssa()
            .unwrap();
        assert!(reports.is_empty());

        // Generate report collection.
        let reports = find_nonstrict_binary_conversion(&cfg);

        assert_eq!(reports.len(), expected_len);
    }
}
