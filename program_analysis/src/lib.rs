use program_structure::cfg::Cfg;
use program_structure::report::ReportCollection;

extern crate num_bigint_dig as num_bigint;

pub mod constraint_analysis;
pub mod taint_analysis;

// Analysis passes.
mod bitwise_complement;
mod constant_conditional;
mod definition_complexity;
mod field_arithmetic;
mod field_comparisons;
mod nonstrict_binary_conversion;
mod unconstrained_less_than;
mod side_effect_analysis;
mod signal_assignments;

pub fn get_analysis_passes<'a>() -> Vec<Box<dyn Fn(&'a Cfg) -> ReportCollection + 'a>> {
    vec![
        Box::new(bitwise_complement::find_bitwise_complement),
        Box::new(signal_assignments::find_signal_assignments),
        Box::new(definition_complexity::run_complexity_analysis),
        Box::new(side_effect_analysis::run_side_effect_analysis),
        Box::new(field_arithmetic::find_field_element_arithmetic),
        Box::new(field_comparisons::find_field_element_comparisons),
        Box::new(unconstrained_less_than::find_unconstrained_less_than),
        Box::new(constant_conditional::find_constant_conditional_statement),
        Box::new(nonstrict_binary_conversion::find_nonstrict_binary_conversion),
    ]
}
