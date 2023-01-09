use analysis_context::{AnalysisContext, AnalysisError};
use program_structure::cfg::Cfg;
use program_structure::report::ReportCollection;

extern crate num_bigint_dig as num_bigint;

pub mod constraint_analysis;
pub mod taint_analysis;
pub mod analysis_context;

// Analysis passes.
mod bitwise_complement;
mod bn128_specific_circuit;
mod constant_conditional;
mod definition_complexity;
mod field_arithmetic;
mod field_comparisons;
mod nonstrict_binary_conversion;
mod under_constrained_signals;
mod unconstrained_less_than;
mod unconstrained_division;
mod side_effect_analysis;
mod signal_assignments;

/// An analysis pass is a function which takes an analysis context and a CFG and
/// returns a set of reports.
type AnalysisPass<'a> =
    dyn Fn(&mut dyn AnalysisContext<Error = AnalysisError>, &'a Cfg) -> ReportCollection + 'a;

pub fn get_analysis_passes<'a>() -> Vec<Box<AnalysisPass<'a>>> {
    vec![
        // Intra-process analysis passes.
        Box::new(|_, cfg| bitwise_complement::find_bitwise_complement(cfg)),
        Box::new(|_, cfg| signal_assignments::find_signal_assignments(cfg)),
        Box::new(|_, cfg| definition_complexity::run_complexity_analysis(cfg)),
        Box::new(|_, cfg| side_effect_analysis::run_side_effect_analysis(cfg)),
        Box::new(|_, cfg| field_arithmetic::find_field_element_arithmetic(cfg)),
        Box::new(|_, cfg| field_comparisons::find_field_element_comparisons(cfg)),
        Box::new(|_, cfg| unconstrained_division::find_unconstrained_division(cfg)),
        Box::new(|_, cfg| bn128_specific_circuit::find_bn128_specific_circuits(cfg)),
        Box::new(|_, cfg| unconstrained_less_than::find_unconstrained_less_than(cfg)),
        Box::new(|_, cfg| constant_conditional::find_constant_conditional_statement(cfg)),
        Box::new(|_, cfg| under_constrained_signals::find_under_constrained_signals(cfg)),
        Box::new(|_, cfg| nonstrict_binary_conversion::find_nonstrict_binary_conversion(cfg)),
    ]
}
