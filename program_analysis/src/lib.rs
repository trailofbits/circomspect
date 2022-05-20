use program_structure::cfg::Cfg;
use program_structure::error_definition::ReportCollection;

pub mod dead_assignments;
pub mod field_arithmetic;
pub mod field_comparisons;
pub mod signal_assignments;

pub fn get_analysis_passes<'a>() -> Vec<Box<dyn Fn(&'a Cfg) -> ReportCollection + 'a>> {
    vec![
        Box::new(dead_assignments::find_dead_assignments),
        Box::new(signal_assignments::find_signal_assignments),
        Box::new(field_arithmetic::find_field_element_arithmetic),
        Box::new(field_comparisons::find_field_element_comparisons),
    ]
}
