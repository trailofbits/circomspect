use log::debug;
use std::collections::HashSet;

use program_structure::{
    ir::*,
    ir::value_meta::ValueMeta,
    report_code::ReportCode,
    cfg::{Cfg, DefinitionType},
    report::{Report, ReportCollection},
    file_definition::{FileID, FileLocation},
};

use crate::analysis_context::AnalysisContext;

// Known templates that are commonly instantiated without accessing the
// corresponding output signals.
const ALLOW_LIST: [&str; 1] = ["Num2Bits"];

struct UnusedOutputSignalWarning {
    // Location of template instantiation.
    file_id: Option<FileID>,
    file_location: FileLocation,
    // The currently analyzed template.
    current_template: String,
    // The instantiated template with an unused output signal.
    component_template: String,
    // The name of the unused output signal.
    signal_name: String,
}

impl UnusedOutputSignalWarning {
    pub fn into_report(self) -> Report {
        let mut report = Report::warning(
            format!(
                "The output signal `{}` defined by the template `{}` is not constrained in `{}`.",
                self.signal_name, self.component_template, self.current_template
            ),
            ReportCode::UnusedOutputSignal,
        );
        if let Some(file_id) = self.file_id {
            report.add_primary(
                self.file_location,
                file_id,
                format!("The template `{}` is instantiated here.", self.component_template),
            );
        }
        report
    }
}

#[derive(Clone, Debug)]
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

/// A reflexive and symmetric relation capturing partial information about
/// equality.
trait MaybeEqual {
    fn maybe_equal(&self, other: &Self) -> bool;
}

/// This is a reflexive and symmetric (but not transitive!) relation
/// identifying all array accesses where the indices are not explicitly known
/// to be different (e.g. from constant propagation). The relation is not
/// transitive since `v[0] == v[i]` and `v[i] == v[1]`, but `v[0] != v[1]`.
///
/// Since `maybe_equal` is not transitive we cannot use it to define
/// `PartialEq` for `VariableAccess`. This also means that we cannot use hash
/// sets or hash maps to track variable accesses using this as our equality
/// relation.
impl MaybeEqual for VariableAccess {
    fn maybe_equal(&self, other: &VariableAccess) -> bool {
        use AccessType::*;
        if self.var.name() != other.var.name() {
            return false;
        }
        if self.access.len() != other.access.len() {
            return false;
        }
        for (self_access, other_access) in self.access.iter().zip(other.access.iter()) {
            match (self_access, other_access) {
                (ArrayAccess(_), ComponentAccess(_)) => {
                    return false;
                }
                (ComponentAccess(_), ArrayAccess(_)) => {
                    return false;
                }
                (ComponentAccess(self_name), ComponentAccess(other_name))
                    if self_name != other_name =>
                {
                    return false;
                }
                (ArrayAccess(self_index), ArrayAccess(other_index)) => {
                    use value_meta::ValueReduction::*;
                    match (self_index.value(), other_index.value()) {
                        (FieldElement(Some(self_value)), FieldElement(Some(other_value)))
                            if self_value != other_value =>
                        {
                            return false;
                        }
                        (Boolean(Some(self_value)), Boolean(Some(other_value)))
                            if self_value != other_value =>
                        {
                            return false;
                        }
                        // Identify all other array accesses.
                        _ => {}
                    }
                }
                // Identify all array accesses.
                _ => {}
            }
        }
        true
    }
}

/// A relation capturing partial information about containment.
trait MaybeContains<T> {
    fn maybe_contains(&self, element: &T) -> bool;
}

impl<T> MaybeContains<T> for Vec<T>
where
    T: MaybeEqual,
{
    fn maybe_contains(&self, element: &T) -> bool {
        self.iter().any(|item| item.maybe_equal(element))
    }
}

struct ComponentData {
    pub meta: Meta,
    pub var_name: VariableName,
    pub var_access: Vec<AccessType>,
    pub template_name: String,
}

impl ComponentData {
    pub fn new(
        meta: &Meta,
        var_name: &VariableName,
        var_access: &[AccessType],
        template_name: &str,
    ) -> Self {
        ComponentData {
            meta: meta.clone(),
            var_name: var_name.clone(),
            var_access: var_access.to_vec(),
            template_name: template_name.to_string(),
        }
    }
}

struct SignalData {
    pub meta: Meta,
    pub template_name: String,
    pub signal_name: String,
    pub signal_access: VariableAccess,
}

impl SignalData {
    pub fn new(
        meta: &Meta,
        template_name: &str,
        signal_name: &str,
        signal_access: VariableAccess,
    ) -> SignalData {
        SignalData {
            meta: meta.clone(),
            template_name: template_name.to_string(),
            signal_name: signal_name.to_string(),
            signal_access,
        }
    }
}

pub fn find_unused_output_signals(
    context: &mut dyn AnalysisContext,
    current_cfg: &Cfg,
) -> ReportCollection {
    // Exit early if the given CFG represents a function.
    if matches!(current_cfg.definition_type(), DefinitionType::Function) {
        return ReportCollection::new();
    }
    debug!("running unused output signal analysis pass");
    let allow_list = HashSet::from(ALLOW_LIST);

    // Collect all instantiated components.
    let mut components = Vec::new();
    let mut accesses = Vec::new();
    for basic_block in current_cfg.iter() {
        for stmt in basic_block.iter() {
            visit_statement(stmt, current_cfg, &mut components, &mut accesses);
        }
    }
    let mut output_signals = Vec::new();
    for component in components {
        // Ignore templates on the allow list.
        if allow_list.contains(&component.template_name[..]) {
            continue;
        }
        if let Ok(component_cfg) = context.template(&component.template_name) {
            for output_signal in component_cfg.output_signals() {
                if let Some(declaration) = component_cfg.get_declaration(output_signal) {
                    // The signal access pattern is given by the component
                    // access pattern, followed by the output signal name,
                    // followed by an array access corresponding to each
                    // dimension entry for the signal.
                    //
                    // E.g., for the component `c[i]` with an output signal
                    // `out` which is a double array, we get `c[i].out[j][k]`.
                    // Since we identify array accesses we simply use `i` for
                    // each array access corresponding to the dimensions of the
                    // signal.
                    let mut var_access = component.var_access.clone();
                    var_access.push(AccessType::ComponentAccess(output_signal.name().to_string()));
                    for _ in declaration.dimensions() {
                        let meta = Meta::new(&(0..0), &None);
                        let index =
                            Expression::Variable { meta, name: VariableName::from_string("i") };
                        var_access.push(AccessType::ArrayAccess(Box::new(index)));
                    }
                    let signal_access = VariableAccess::new(&component.var_name, &var_access);
                    output_signals.push(SignalData::new(
                        &component.meta,
                        &component.template_name,
                        output_signal.name(),
                        signal_access,
                    ));
                }
            }
        }
    }
    let mut reports = ReportCollection::new();
    for output_signal in output_signals {
        if !maybe_accesses(&accesses, &output_signal.signal_access) {
            reports.push(build_report(
                &output_signal.meta,
                current_cfg.name(),
                &output_signal.template_name,
                &output_signal.signal_name,
            ))
        }
    }

    debug!("{} new reports generated", reports.len());
    reports
}

// Check if there is an access to a prefix of the output signal access which
// contains the output signal name. E.g. for the output signal `n2b[1].out[0]`
// it is enough that the list of all variable accesses `maybe_contains` the
// prefix `n2b[1].out`. This is to catch instances where the template passes the
// output signal as input to a function.
fn maybe_accesses(accesses: &Vec<VariableAccess>, signal_access: &VariableAccess) -> bool {
    use AccessType::*;
    let mut signal_access = signal_access.clone();
    while !accesses.maybe_contains(&signal_access) {
        if let Some(ComponentAccess(_)) = signal_access.access.last() {
            // The output signal name is the last component access in the access
            // array. If it is not included in the access, the output signal is
            // not accessed by the template.
            return false;
        } else {
            signal_access.access.pop();
        }
    }
    true
}

fn visit_statement(
    stmt: &Statement,
    cfg: &Cfg,
    components: &mut Vec<ComponentData>,
    accesses: &mut Vec<VariableAccess>,
) {
    use Statement::*;
    use Expression::*;
    use VariableType::*;
    // Collect all instantiated components.
    if let Substitution { var: var_name, rhe, .. } = stmt {
        let (var_access, rhe) = if let Update { access, rhe, .. } = rhe {
            (access.clone(), *rhe.clone())
        } else {
            (Vec::new(), rhe.clone())
        };
        if let (Some(Component), Call { meta, name: template_name, .. }) =
            (cfg.get_type(var_name), rhe)
        {
            components.push(ComponentData::new(&meta, var_name, &var_access, &template_name));
        }
    }
    // Collect all variable accesses.
    match stmt {
        Substitution { rhe, .. } => visit_expression(rhe, accesses),
        ConstraintEquality { lhe, rhe, .. } => {
            visit_expression(lhe, accesses);
            visit_expression(rhe, accesses);
        }
        Declaration { .. } => { /* We ignore dimensions in declarations. */ }
        IfThenElse { .. } => { /* We ignore if-statement conditions. */ }
        Return { .. } => { /* We ignore return statements. */ }
        LogCall { .. } => { /* We ignore log statements. */ }
        Assert { .. } => { /* We ignore asserts. */ }
    }
}

fn visit_expression(expr: &Expression, accesses: &mut Vec<VariableAccess>) {
    use Expression::*;
    match expr {
        PrefixOp { rhe, .. } => {
            visit_expression(rhe, accesses);
        }
        InfixOp { lhe, rhe, .. } => {
            visit_expression(lhe, accesses);
            visit_expression(rhe, accesses);
        }
        SwitchOp { cond, if_true, if_false, .. } => {
            visit_expression(cond, accesses);
            visit_expression(if_true, accesses);
            visit_expression(if_false, accesses);
        }
        Call { args, .. } => {
            for arg in args {
                visit_expression(arg, accesses);
            }
        }
        InlineArray { values, .. } => {
            for value in values {
                visit_expression(value, accesses);
            }
        }
        Access { var, access, .. } => {
            accesses.push(VariableAccess::new(var, access));
        }
        Update { rhe, .. } => {
            // We ignore accesses in assignments.
            visit_expression(rhe, accesses);
        }
        Variable { .. } | Number(_, _) | Phi { .. } => (),
    }
}

fn build_report(
    meta: &Meta,
    current_template: &str,
    component_template: &str,
    signal_name: &str,
) -> Report {
    UnusedOutputSignalWarning {
        file_id: meta.file_id(),
        file_location: meta.file_location(),
        current_template: current_template.to_string(),
        component_template: component_template.to_string(),
        signal_name: signal_name.to_string(),
    }
    .into_report()
}

#[cfg(test)]
mod tests {
    use num_bigint_dig::BigInt;
    use program_structure::{
        constants::Curve,
        intermediate_representation::{
            VariableName, AccessType, Expression, Meta, value_meta::ValueReduction,
        },
    };

    use crate::{
        analysis_runner::AnalysisRunner,
        unused_output_signal::{MaybeEqual, MaybeContains, maybe_accesses},
    };

    use super::{find_unused_output_signals, VariableAccess};

    #[test]
    fn test_maybe_equal() {
        use AccessType::*;
        use Expression::*;
        use ValueReduction::*;

        let var = VariableName::from_string("var");
        let meta = Meta::new(&(0..0), &None);
        let mut zero = Box::new(Number(meta.clone(), BigInt::from(0)));
        let mut one = Box::new(Number(meta.clone(), BigInt::from(1)));
        let i = Box::new(Variable { meta, name: VariableName::from_string("i") });

        // Set the value of `zero` and `one` explicitly.
        let _ = zero
            .meta_mut()
            .value_knowledge_mut()
            .set_reduces_to(FieldElement { value: BigInt::from(0) });
        let _ = one
            .meta_mut()
            .value_knowledge_mut()
            .set_reduces_to(FieldElement { value: BigInt::from(1) });

        // `var[0].out`
        let first_access = VariableAccess::new(
            &var.with_version(1),
            &[ArrayAccess(zero.clone()), ComponentAccess("out".to_string())],
        );
        // `var[i].out`
        let second_access = VariableAccess::new(
            &var.with_version(2),
            &[ArrayAccess(i.clone()), ComponentAccess("out".to_string())],
        );
        // `var[1].out`
        let third_access = VariableAccess::new(
            &var.with_version(3),
            &[ArrayAccess(one), ComponentAccess("out".to_string())],
        );
        // `var[i].out[0]`
        let fourth_access = VariableAccess::new(
            &var.with_version(4),
            &[ArrayAccess(i), ComponentAccess("out".to_string()), ArrayAccess(zero)],
        );

        // The first and second accesses should be identified.
        assert!(first_access.maybe_equal(&second_access));
        // The first and third accesses should not be identified.
        assert!(!first_access.maybe_equal(&third_access));

        let accesses = vec![first_access];

        // The first and second accesses should be identified.
        assert!(accesses.maybe_contains(&second_access));
        // The first and third accesses should not be identified.
        assert!(!accesses.maybe_contains(&third_access));

        // The fourth access is not equal to the first, but a prefix is.
        assert!(!accesses.maybe_contains(&fourth_access));
        assert!(maybe_accesses(&accesses, &fourth_access));
    }

    #[test]
    fn test_maybe_accesses() {}

    #[test]
    fn test_unused_output_signal() {
        // The output signal `out` in `Test` is not accessed, for any of the two
        // instantiated components.
        let src = [
            r#"
            template Test() {
                signal input in;
                signal output out;

                out <== 2 * in + 1;
            }
        "#,
            r#"
            template Main() {
                signal input in[2];

                component test[2];
                test[0] = Test();
                test[1] = Test();
                test[0].in <== in[0];
                test[1].in <== in[1];
            }
        "#,
        ];
        validate_reports("Main", &src, 2);

        // `Num2Bits` is on the allow list and should not produce a report.
        let src = [
            r#"
            template Num2Bits(n) {
                signal input in;
                signal output out[n];

                for (var i = 0; i < n; i++) {
                    out[i] <== in;
                }
            }
        "#,
            r#"
            template Main() {
                signal input in;

                component n2b = Num2Bits();
                n2b.in <== in[0];

                in[1] === in[0] + 1;
            }
        "#,
        ];
        validate_reports("Main", &src, 0);

        // If the template is not known we should not produce a report.
        let src = [r#"
            template Main() {
                signal input in[2];

                component test[2];
                test[0] = Test();
                test[1] = Test();
                test[0].in <== in[0];
                test[1].in <== in[1];
            }
        "#];
        validate_reports("Main", &src, 0);

        // Should generate a warning for `test[1]` but not for `test[0]`.
        let src = [
            r#"
            template Test() {
                signal input in;
                signal output out;

                out <== 2 * in + 1;
            }
        "#,
            r#"
            template Main() {
                signal input in[2];

                component test[2];
                test[0] = Test();
                test[1] = Test();
                test[0].in <== in[0];
                test[1].in <== in[1];

                test[0].out === 1;
            }
        "#,
        ];
        validate_reports("Main", &src, 1);

        // Should not generate a warning for `test.out`.
        let src = [
            r#"
            template Test() {
                signal input in;
                signal output out[2];

                out[0] <== 2 * in + 1;
                out[1] <== 3 * in + 2;
            }
        "#,
            r#"
            template Main() {
                signal input in;

                component test;
                test = Test();
                test.in <== in[0];

                func(test.out) === 1;
            }
        "#,
        ];
        validate_reports("Main", &src, 0);

        // TODO: Should detect that `test[i].out[1]` is not accessed.
        let src = [
            r#"
            template Test() {
                signal input in;
                signal output out[2];

                out[0] <== 2 * in + 1;
                out[1] <== 3 * in + 2;
            }
        "#,
            r#"
            template Main() {
                signal input in[2];

                component test[2];
                for (var i = 0; i < 2; i++) {
                    test[i] = Test();
                    test[i].in <== in[i];
                }
                for (var i = 0; i < 2; i++) {
                    test[i].out[0] === 1;
                }
            }
        "#,
        ];
        validate_reports("Main", &src, 0);

        // TODO: Should detect that `test[1].out` is not accessed.
        let src = [
            r#"
            template Test() {
                signal input in;
                signal output out;

                out <== 2 * in + 1;
            }
        "#,
            r#"
            template Main() {
                signal input in[2];

                component test[2];
                for (var i = 0; i < 2; i++) {
                    test[i] = Test();
                    test[i].in = in[i];
                }

                test[0].out === 1;
            }
        "#,
        ];
        validate_reports("Main", &src, 0);
    }

    fn validate_reports(name: &str, src: &[&str], expected_len: usize) {
        let mut context = AnalysisRunner::new(Curve::Goldilocks).with_src(src);
        let cfg = context.take_template(name).unwrap();
        let reports = find_unused_output_signals(&mut context, &cfg);
        assert_eq!(reports.len(), expected_len);
    }
}
