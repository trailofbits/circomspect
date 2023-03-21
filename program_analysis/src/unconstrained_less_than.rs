use std::collections::HashMap;
use std::fmt;

use log::{debug, trace};

use num_bigint::BigInt;
use program_structure::cfg::Cfg;
use program_structure::ir::value_meta::{ValueMeta, ValueReduction};
use program_structure::report_code::ReportCode;
use program_structure::report::{Report, ReportCollection};
use program_structure::ir::*;

pub struct UnconstrainedLessThanWarning {
    value: Expression,
    bit_sizes: Vec<(Meta, Expression)>,
}
impl UnconstrainedLessThanWarning {
    fn primary_meta(&self) -> &Meta {
        self.value.meta()
    }

    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            "Inputs to `LessThan` need to be constrained to ensure that they are non-negative"
                .to_string(),
            ReportCode::UnconstrainedLessThan,
        );
        if let Some(file_id) = self.primary_meta().file_id {
            report.add_primary(
                self.primary_meta().file_location(),
                file_id,
                format!("`{}` needs to be constrained to ensure that it is <= p/2.", self.value),
            );
            for (meta, size) in self.bit_sizes {
                report.add_secondary(
                    meta.file_location(),
                    file_id,
                    Some(format!("`{}` is constrained to `{}` bits here.", self.value, size)),
                );
            }
        }
        report
    }
}

#[derive(Eq, PartialEq, Hash)]
struct VariableAccess {
    pub var: VariableName,
    pub access: Vec<AccessType>,
}

impl VariableAccess {
    fn new(var: &VariableName, access: &[AccessType]) -> Self {
        // We disregard the version to make sure accesses are not order dependent.
        VariableAccess { var: var.without_version(), access: access.to_vec() }
    }
}

/// Tracks component instantiations `var = T(...)` where then template `T` is
/// either `LessThan` or `Num2Bits`.
enum Component {
    LessThan,
    Num2Bits { bit_size: Box<Expression> },
}

impl Component {
    fn less_than() -> Self {
        Self::LessThan
    }

    fn num_2_bits(bit_size: &Expression) -> Self {
        Self::Num2Bits { bit_size: Box::new(bit_size.clone()) }
    }
}

/// Tracks component input signal initializations on the form `T.in <== input`
/// where `T` is either `LessThan` or `Num2Bits`.
enum ComponentInput {
    LessThan { value: Box<Expression> },
    Num2Bits { value: Box<Expression>, bit_size: Box<Expression> },
}

impl ComponentInput {
    fn less_than(value: &Expression) -> Self {
        Self::LessThan { value: Box::new(value.clone()) }
    }

    fn num_2_bits(value: &Expression, bit_size: &Expression) -> Self {
        Self::Num2Bits { value: Box::new(value.clone()), bit_size: Box::new(bit_size.clone()) }
    }
}

/// Tracks constraints for a single input to `LessThan`.
#[derive(Default)]
struct ConstraintData {
    /// Input to `LessThan`.
    pub less_than: Vec<Meta>,
    /// Input to `Num2Bits`.
    pub num_2_bits: Vec<Meta>,
    /// Size constraints enforced by `Num2Bits`.
    pub bit_sizes: Vec<Expression>,
}

/// The `LessThan` template from Circomlib does not constrain the individual
/// inputs to the input size `n` bits, or to be positive. If the inputs are
/// allowed to be greater than p/2 it is possible to find field elements `a` and
/// `b` such that
///
///   1. `a > b` either as unsigned integers, or as signed elements in GF(p),
///   2. lt = LessThan(n),
///   3. lt.in[0] = a,
///   4. lt.in[1] = b, and
///   5. lt.out = 1
///
/// This analysis pass looks for instantiations of `LessThan` where the inputs
/// are not constrained to be <= p/2 using `Num2Bits`.
pub fn find_unconstrained_less_than(cfg: &Cfg) -> ReportCollection {
    debug!("running unconstrained less-than analysis pass");
    let mut components = HashMap::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            update_components(stmt, &mut components);
        }
    }
    let mut inputs = Vec::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            update_inputs(stmt, &components, &mut inputs);
        }
    }
    let mut constraints = HashMap::<Expression, ConstraintData>::new();
    for input in inputs {
        match input {
            ComponentInput::LessThan { value } => {
                let entry = constraints.entry(*value.clone()).or_default();
                entry.less_than.push(value.meta().clone());
            }
            ComponentInput::Num2Bits { value, bit_size, .. } => {
                let entry = constraints.entry(*value.clone()).or_default();
                entry.num_2_bits.push(value.meta().clone());
                entry.bit_sizes.push(*bit_size.clone());
            }
        }
    }

    // Generate a report for each input to `LessThan` where the input size is
    // not constrained to be positive using `Num2Bits`.
    let mut reports = ReportCollection::new();
    let max_value = BigInt::from(cfg.constants().prime_size() - 1);
    for (value, data) in constraints {
        // Check if the the value is used as input for `LessThan`.
        if data.less_than.is_empty() {
            continue;
        }
        // Check if the value is constrained to be positive.
        let mut is_positive = false;
        for bit_size in &data.bit_sizes {
            if let Some(ValueReduction::FieldElement { value }) = bit_size.value() {
                if value < &max_value {
                    is_positive = true;
                    break;
                }
            }
        }
        if is_positive {
            continue;
        }
        // We failed to prove that the input is positive. Generate a report.
        reports.push(build_report(&value, &data));
    }
    debug!("{} new reports generated", reports.len());
    reports
}

fn update_components(stmt: &Statement, components: &mut HashMap<VariableAccess, Component>) {
    use AssignOp::*;
    use Statement::*;
    use Expression::*;
    if let Substitution { meta, var, op: AssignLocalOrComponent, rhe, .. } = stmt {
        // If the variable `var` is declared as a local variable or signal, we exit early.
        if meta.type_knowledge().is_local() || meta.type_knowledge().is_signal() {
            return;
        }
        // If this is an assignment on the form `var[i] = T(...)` we need to store the access and obtain the RHS.
        let (rhe, access) = if let Update { access, rhe, .. } = rhe {
            (rhe.as_ref(), access.clone())
        } else {
            (rhe, Vec::new())
        };
        if let Call { name: component_name, args, .. } = rhe {
            if component_name == "LessThan" && args.len() == 1 {
                // We assume this is the `LessThan` circuit from Circomlib.
                trace!(
                    "`LessThan` template instantiation `{var}{}` found",
                    vec_to_display(&access, "")
                );
                let component = VariableAccess::new(var, &access);
                components.insert(component, Component::less_than());
            } else if component_name == "Num2Bits" && args.len() == 1 {
                // We assume this is the `Num2Bits` circuit from Circomlib.
                trace!(
                    "`LessThan` template instantiation `{var}{}` found",
                    vec_to_display(&access, "")
                );
                let component = VariableAccess::new(var, &access);
                components.insert(component, Component::num_2_bits(&args[0]));
            }
        }
    }
}

fn update_inputs(
    stmt: &Statement,
    components: &HashMap<VariableAccess, Component>,
    inputs: &mut Vec<ComponentInput>,
) {
    use AssignOp::*;
    use Statement::*;
    use Expression::*;
    use AccessType::*;
    if let Substitution {
        var, op: AssignConstraintSignal, rhe: Update { access, rhe, .. }, ..
    } = stmt
    {
        // If this is a `Num2Bits` input signal assignment, the input signal
        // access would be the last element of the `access` vector.
        let mut component_access = access.clone();
        let signal_access = component_access.pop();
        let component = VariableAccess::new(var, &component_access);
        if let Some(Component::Num2Bits { bit_size, .. }) = components.get(&component) {
            let Some(ComponentAccess(signal_name)) = signal_access else {
                return;
            };
            if signal_name != "in" {
                return;
            }
            trace!("`Num2Bits` input signal assignment `{rhe}` found");
            inputs.push(ComponentInput::num_2_bits(rhe, bit_size));
        }

        // If this is a `LessThan` input signal assignment, the input index
        // access would be the last element, and the input signal access
        // would be the next to last element of the `access` vector.
        let mut component_access = access.clone();
        let index_access = component_access.pop();
        let signal_access = component_access.pop();
        let component = VariableAccess::new(var, &component_access);
        if let Some(Component::LessThan { .. }) = components.get(&component) {
            let (Some(ComponentAccess(signal_name)), Some(ArrayAccess(_))) = (signal_access, index_access) else {
                return;
            };
            if signal_name != "in" {
                return;
            }
            trace!("`LessThan` input signal assignment `{rhe}` found");
            inputs.push(ComponentInput::less_than(rhe));
        }
    }
}

#[must_use]
fn build_report(value: &Expression, data: &ConstraintData) -> Report {
    UnconstrainedLessThanWarning {
        value: value.clone(),
        bit_sizes: data.num_2_bits.iter().cloned().zip(data.bit_sizes.iter().cloned()).collect(),
    }
    .into_report()
}

#[must_use]
fn vec_to_display<T: fmt::Display>(elems: &[T], sep: &str) -> String {
    elems.iter().map(|elem| format!("{elem}")).collect::<Vec<String>>().join(sep)
}

#[cfg(test)]
mod tests {
    use parser::parse_definition;
    use program_structure::{cfg::IntoCfg, constants::Curve};

    use super::*;

    #[test]
    fn test_unconstrained_less_than() {
        let src = r#"
            template Test(n) {
              signal input small;
              signal input large;
              signal output ok;

              // Check that small < large.
              component lt = LessThan(n);
              lt.in[0] <== small;
              lt.in[1] <== large;

              ok <== lt.out;
            }
        "#;
        validate_reports(src, 2);

        let src = r#"
            template Test(n) {
              signal input small;
              signal input large;
              signal output ok;

              // Constrain inputs to n bits.
              component n2b[2];
              n2b[0] = Num2Bits(n);
              n2b[0].in <== small;
              n2b[1] = Num2Bits(n + 1);
              n2b[1].in <== large;

              // Check that small < large.
              component lt = LessThan(n);
              lt.in[0] <== small;
              lt.in[1] <== large;

              ok <== lt.out;
            }
        "#;
        validate_reports(src, 2);

        let src = r#"
            template Test(n) {
              signal input small;
              signal input large;
              signal output ok;

              // Constrain inputs to n bits.
              component n2b[2];
              n2b[0] = Num2Bits(n);
              n2b[0].in <== small;
              n2b[1] = Num2Bits(32);
              n2b[1].in <== large;

              // Check that small < large.
              component lt = LessThan(n);
              lt.in[0] <== small;
              lt.in[1] <== large;

              ok <== lt.out;
            }
        "#;
        validate_reports(src, 1);

        let src = r#"
            template Test(n) {
              signal input small;
              signal input large;
              signal output ok;

              // Check that small < large.
              component lt = LessThan(n);
              lt.in[1] <== large;
              lt.in[0] <== small;

              // Constrain inputs to n bits.
              component n2b[2];
              n2b[0] = Num2Bits(32);
              n2b[0].in <== small;
              n2b[1] = Num2Bits(64);
              n2b[1].in <== large;

              ok <== lt.out;
            }
        "#;
        validate_reports(src, 0);
    }

    fn validate_reports(src: &str, expected_len: usize) {
        // Build CFG.
        let mut reports = ReportCollection::new();
        let cfg = parse_definition(src)
            .unwrap()
            .into_cfg(&Curve::default(), &mut reports)
            .unwrap()
            .into_ssa()
            .unwrap();
        assert!(reports.is_empty());

        // Generate report collection.
        let reports = find_unconstrained_less_than(&cfg);
        assert_eq!(reports.len(), expected_len);
    }
}
