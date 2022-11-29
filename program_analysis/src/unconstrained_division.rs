use std::collections::HashMap;
use std::fmt;

use log::{debug, trace};

use num_traits::Zero;
use program_structure::cfg::Cfg;
use program_structure::intermediate_representation::value_meta::{ValueReduction, ValueMeta};
use program_structure::ir::degree_meta::DegreeMeta;
use program_structure::report_code::ReportCode;
use program_structure::report::{Report, ReportCollection};
use program_structure::file_definition::{FileID, FileLocation};
use program_structure::ir::*;

pub struct UnconstrainedDivisionWarning {
    divisor: Expression,
    file_id: Option<FileID>,
    file_location: FileLocation,
}

impl UnconstrainedDivisionWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            "In signal assignments containing division, the divisor needs to be constrained to be non-zero".to_string(),
            ReportCode::UnconstrainedDivision,
        );
        if let Some(file_id) = self.file_id {
            report.add_primary(
                self.file_location,
                file_id,
                format!("The divisor `{}` must be constrained to be non-zero.", self.divisor),
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
        // We disregard the version to make sure accesses are not order dependent.
        VariableAccess { var: var.without_version(), access: access.to_vec() }
    }
}

/// Tracks `IsZero` template instantiations and uses.
#[derive(Default)]
struct Component {
    pub input: Option<Expression>,
    pub output: Option<Expression>,
}

impl Component {
    fn new() -> Self {
        Component::default()
    }

    fn ensures_nonzero(&self, expr: &Expression) -> bool {
        if let Some(input) = self.input.as_ref() {
            // This component ensures that the given expression is non-zero if
            //   1. The component input is the given expression
            //   2. The component output evaluates to false
            expr == input && matches!(self.output(), Some(false))
        } else {
            false
        }
    }

    fn output(&self) -> Option<bool> {
        use ValueReduction::*;
        let value = self.output.as_ref().and_then(|output| output.value());
        match value {
            Some(FieldElement { value }) => Some(!value.is_zero()),
            Some(Boolean { value }) => Some(*value),
            None => None,
        }
    }
}

/// Since division is not expressible as a quadratic constraint, it is common to
/// perform division using the following pattern.
///
///   `c <-- a / b`
///   `b * c === a`
///
/// That is, we assign the result of `a / b` to `c` during the proof generation,
/// and the constrain `a`, `b`, and `c` to ensure that `b * c = a` during proof
/// verification. However, this implicitly assumes that `b` is non-zero when the
/// proof is generated, which needs to be verified separately when the proof is
/// verified.
///
/// This analysis pass looks for signal assignments on the form `c <-- a / b`
/// where the signal `b` is not constrained to be non-zero using the `IsZero`
/// circuit from Circomlib.
pub fn find_unconstrained_division(cfg: &Cfg) -> ReportCollection {
    debug!("running unconstrained divisor analysis pass");
    let mut reports = ReportCollection::new();
    let mut divisors = Vec::new();
    let mut constraints = HashMap::new();
    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            update_divisors(stmt, &mut divisors);
        }
    }
    if divisors.is_empty() {
        return reports;
    }

    for basic_block in cfg.iter() {
        for stmt in basic_block.iter() {
            update_constraints(stmt, &mut constraints);
        }
    }
    for divisor in divisors {
        let mut non_zero = false;
        for constraint in constraints.values() {
            if constraint.ensures_nonzero(&divisor) {
                non_zero = true;
                break;
            }
        }
        if !non_zero {
            reports.push(build_report(&divisor));
        }
    }
    debug!("{} new reports generated", reports.len());
    reports
}

fn update_divisors(stmt: &Statement, divisors: &mut Vec<Expression>) {
    use AssignOp::*;
    use Statement::*;
    use Expression::*;
    use ExpressionInfixOpcode::*;
    // Identify signal assignment on the form `c <-- a / b`.
    if let Substitution { op: AssignSignal, rhe, .. } = stmt {
        // If this is an update node, we extract the right-hand side.
        let rhe = if let Update { rhe, .. } = rhe { rhe } else { rhe };

        // If the assigned expression is on the form `a / b`, where `b` may be non-constant, we store the divisor `b`.
        if let InfixOp { infix_op: Div, rhe, .. } = rhe {
            match rhe.degree() {
                Some(range) if !range.is_constant() => {
                    divisors.push(*rhe.clone());
                }
                None => {
                    divisors.push(*rhe.clone());
                }
                _ => {}
            }
        }
    }
}

fn update_constraints(stmt: &Statement, constraints: &mut HashMap<VariableAccess, Component>) {
    use AssignOp::*;
    use Statement::*;
    use Expression::*;
    use AccessType::*;
    match stmt {
        // Identify `IsZero` template instantiations.
        Substitution { meta, var, op: AssignLocalOrComponent, rhe } => {
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
                if component_name == "IsZero" && args.is_empty() {
                    // We assume this is the `IsZero` circuit from Circomlib.
                    trace!(
                        "`IsZero` template instantiation `{var}{}` found",
                        vec_to_display(&access, "")
                    );
                    let component = VariableAccess::new(var, &access);
                    constraints.insert(component, Component::new());
                }
            }
        }
        // Identify `IsZero` input signal assignments.
        Substitution {
            var, op: AssignConstraintSignal, rhe: Update { access, rhe, .. }, ..
        } => {
            // If this is a `Num2Bits` input signal assignment, the input signal
            // access would be the last element of the `access` vector.
            let mut component_access = access.clone();
            let signal_access = component_access.pop();
            let component = VariableAccess::new(var, &component_access);
            if let Some(constraint) = constraints.get_mut(&component) {
                // This is a signal assignment to either the input or output if `IsZero`.
                if let Some(ComponentAccess(signal_name)) = signal_access {
                    if signal_name == "in" {
                        constraint.input = Some(*rhe.clone());
                    }
                }
            }
        }
        // Identify `IsZero` output signal constraints on the form `var[i].out === expr`.
        ConstraintEquality { lhe: Access { var, access, .. }, rhe, .. } => {
            // Assume LHS is the `IsZero` output signal.
            let mut component_access = access.clone();
            let signal_access = component_access.pop();
            let component = VariableAccess::new(var, &component_access);
            if let Some(constraint) = constraints.get_mut(&component) {
                if let Some(ComponentAccess(signal_name)) = signal_access {
                    if signal_name == "out" {
                        constraint.output = Some(rhe.clone());
                    }
                }
            }
        }
        // Identify `IsZero` output signal constraints on the form `expr === var[i].out ===`.
        ConstraintEquality { lhe, rhe: Access { var, access, .. }, .. } => {
            // Assume RHS is the `IsZero` output signal.
            let mut component_access = access.clone();
            let signal_access = component_access.pop();
            let component = VariableAccess::new(var, &component_access);
            if let Some(constraint) = constraints.get_mut(&component) {
                if let Some(ComponentAccess(signal_name)) = signal_access {
                    if signal_name == "out" {
                        constraint.output = Some(lhe.clone());
                    }
                }
            }
        }
        // By default we do nothing.
        _ => {}
    }
}

#[must_use]
fn build_report(divisor: &Expression) -> Report {
    UnconstrainedDivisionWarning {
        divisor: divisor.clone(),
        file_id: divisor.meta().file_id,
        file_location: divisor.meta().file_location(),
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
              signal input a;
              signal input b;
              signal output c;

              c <-- a / b;
              c * b === a;
            }
        "#;
        validate_reports(src, 1);

        let src = r#"
            template Test(n) {
              signal input a[n];
              signal input b[n];
              signal output c[n];

              for (var i = 0; i < n; i++) {
                c[i] <-- a[i] / b[i];
                c[i] * b[i] === a[i];
              }
            }
        "#;
        validate_reports(src, 1);

        let src = r#"
            template Test(n) {
              signal input a;
              signal input b;
              signal output c;

              component check = IsZero();
              check.in <== b;
              check.out === 1 - 1;

              c <-- a / b;
              c * b === a;
            }
        "#;
        validate_reports(src, 0);

        let src = r#"
            template Test(n) {
              signal input a;
              signal input b;
              signal output c;

              c <-- a / b;
              c * b === a;

              component check = IsZero();
              check.in <== b;
              check.out === 0;
            }
        "#;
        validate_reports(src, 0);

        let src = r#"
            template Test(n) {
              signal input a;
              signal input b;
              signal output c;

              c <-- a / (2 * n + 1);
              c * b === a;
            }
        "#;
        validate_reports(src, 0);

        let src = r#"
            template Test(n) {
              signal input a;
              signal input b;
              signal output c;

              component check = IsZero();
              check.in <== b;
              check.out === 1;

              c <-- a / b;
              c * b === a;
            }
        "#;
        validate_reports(src, 1);

        let src = r#"
            template Test(n) {
              signal input a;
              signal input b;
              signal output c;

              component check = IsZero();
              check.in <== a;
              check.out === 0;

              c <-- a / b;
              c * b === a;
            }
        "#;
        validate_reports(src, 1);
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
        let reports = find_unconstrained_division(&cfg);
        assert_eq!(reports.len(), expected_len);
    }
}
