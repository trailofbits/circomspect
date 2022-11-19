use std::collections::HashMap;
use std::fmt;

use log::{debug, trace};

use program_structure::cfg::Cfg;
use program_structure::report_code::ReportCode;
use program_structure::report::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::*;

pub struct UnconstrainedLessThanWarning {
    input_size: Expression,
    file_id: Option<FileID>,
    primary_location: FileLocation,
    secondary_location: FileLocation,
}

impl UnconstrainedLessThanWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            "Inputs to `LessThan` must be constrained to the input size".to_string(),
            ReportCode::UnconstrainedLessThan,
        );
        if let Some(file_id) = self.file_id {
            report.add_primary(
                self.primary_location,
                file_id,
                format!(
                    "This input to `LessThan` must be constrained to `{}` bits.",
                    self.input_size
                ),
            );
            report.add_secondary(
                self.secondary_location,
                file_id,
                Some("Circomlib template `LessThan` instantiated here.".to_string()),
            );
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
        VariableAccess { var: var.clone(), access: access.to_vec() }
    }
}

/// Tracks component instantiations `var = T(...)` where `T` is either `LessThan`
/// or `Num2Bits`.
enum Component {
    LessThan { meta: Box<Meta>, required_size: Box<Expression> },
    Num2Bits { enforced_size: Box<Expression> },
}

impl Component {
    fn less_than(meta: &Meta, required_size: &Expression) -> Self {
        Self::LessThan {
            meta: Box::new(meta.clone()),
            required_size: Box::new(required_size.clone()),
        }
    }

    fn num_2_bits(enforced_size: &Expression) -> Self {
        Self::Num2Bits { enforced_size: Box::new(enforced_size.clone()) }
    }
}

/// Tracks component input signal initializations on the form `T.in <== input`
/// where `T` is either `LessThan` or `Num2Bits`.
enum ComponentInput {
    LessThan {
        component_meta: Box<Meta>,
        input_meta: Box<Meta>,
        value: Box<Expression>,
        required_size: Box<Expression>,
    },
    Num2Bits {
        value: Box<Expression>,
        enforced_size: Box<Expression>,
    },
}

impl ComponentInput {
    fn less_than(
        component_meta: &Meta,
        input_meta: &Meta,
        value: &Expression,
        required_size: &Expression,
    ) -> Self {
        Self::LessThan {
            component_meta: Box::new(component_meta.clone()),
            input_meta: Box::new(input_meta.clone()),
            value: Box::new(value.clone()),
            required_size: Box::new(required_size.clone()),
        }
    }

    fn num_2_bits(value: &Expression, enforced_size: &Expression) -> Self {
        Self::Num2Bits {
            value: Box::new(value.clone()),
            enforced_size: Box::new(enforced_size.clone()),
        }
    }
}

// The signal input at `signal_meta` for the component defined at
// `component_meta` must be at most `size` bits.
struct SizeEntry {
    pub component_meta: Meta,
    pub input_meta: Meta,
    pub required_size: Expression,
}

impl SizeEntry {
    pub fn new(component_meta: &Meta, input_meta: &Meta, required_size: &Expression) -> Self {
        SizeEntry {
            component_meta: component_meta.clone(),
            input_meta: input_meta.clone(),
            required_size: required_size.clone(),
        }
    }
}

impl fmt::Debug for SizeEntry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.required_size)
    }
}

/// Size constraints for a single component input.
#[derive(Debug, Default)]
struct SizeConstraints {
    /// Size constraint required by `LessThan`.
    pub required: Vec<SizeEntry>,
    /// Size constraint enforced by `Num2Bits`.
    pub enforced: Vec<Expression>,
}

/// The `LessThan` template from Circomlib does not constrain the individual
/// inputs to the input size `n`. If the input size can be more than `n` bits,
/// it is possible to find field elements `a` and `b` such that
///
///   1. `a > b`,
///   2. lt = LessThan(n),
///   3. lt.in[0] = a,
///   4. lt.in[1] = b, and
///   5. lt.out = 1
///
/// This analysis pass looks for instantiations of `LessThan` where the inputs
/// are not constrained to `n` bits using `Num2Bits`.
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
    let mut constraints = HashMap::<Expression, SizeConstraints>::new();
    for input in inputs {
        match input {
            ComponentInput::LessThan { component_meta, input_meta, value, required_size } => {
                constraints.entry(*value.clone()).or_default().required.push(SizeEntry::new(
                    &component_meta,
                    &input_meta,
                    &required_size,
                ));
            }
            ComponentInput::Num2Bits { value, enforced_size, .. } => {
                constraints.entry(*value.clone()).or_default().enforced.push(*enforced_size);
            }
        }
    }

    // Generate a report for each input to `LessThan` where the input size is
    // not constrained to the `LessThan` bit size using `Num2Bits`.
    let mut reports = ReportCollection::new();
    for sizes in constraints.values() {
        for required in &sizes.required {
            if !sizes.enforced.contains(&required.required_size) {
                reports.push(build_report(
                    &required.component_meta,
                    &required.input_meta,
                    &required.required_size,
                ))
            }
        }
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
                components.insert(component, Component::less_than(meta, &args[0]));
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
        if let Some(Component::Num2Bits { enforced_size, .. }) = components.get(&component) {
            let Some(ComponentAccess(signal_name)) = signal_access else {
                return;
            };
            if signal_name != "in" {
                return;
            }
            trace!("`Num2Bits` input signal assignment `{rhe}` found");
            inputs.push(ComponentInput::num_2_bits(rhe, enforced_size));
        }

        // If this is a `LessThan` input signal assignment, the input index
        // access would be the last element, and the input signal access
        // would be the next to last element of the `access` vector.
        let mut component_access = access.clone();
        let index_access = component_access.pop();
        let signal_access = component_access.pop();
        let component = VariableAccess::new(var, &component_access);
        if let Some(Component::LessThan { meta: component_meta, required_size, .. }) =
            components.get(&component)
        {
            let (Some(ComponentAccess(signal_name)), Some(ArrayAccess(_))) = (signal_access, index_access) else {
                return;
            };
            if signal_name != "in" {
                return;
            }
            trace!("`LessThan` input signal assignment `{rhe}` found");
            inputs.push(ComponentInput::less_than(component_meta, rhe.meta(), rhe, required_size));
        }
    }
}

#[must_use]
fn build_report(component_meta: &Meta, input_meta: &Meta, size: &Expression) -> Report {
    UnconstrainedLessThanWarning {
        input_size: size.clone(),
        file_id: component_meta.file_id,
        primary_location: input_meta.file_location(),
        secondary_location: component_meta.file_location(),
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
        validate_reports(src, 1);

        let src = r#"
            template Test(n) {
              signal input small;
              signal input large;
              signal output ok;

              // Constrain inputs to n bits.
              component n2b[2];
              n2b[0] = Num2Bits(n);
              n2b[0].in <== small;
              n2b[1] = Num2Bits(n);
              n2b[1].in <== large;

              // Check that small < large.
              component lt = LessThan(n);
              lt.in[0] <== small;
              lt.in[1] <== large;

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
