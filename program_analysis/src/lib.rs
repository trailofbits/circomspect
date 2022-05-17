use program_structure::cfg::cfg::CFG;
use program_structure::error_definition::ReportCollection;

pub mod field_comparisons;

pub fn get_analysis_passes() -> Vec<impl FnOnce(&CFG) -> ReportCollection> {
    vec![
        field_comparisons::find_field_element_comparisons
    ]
}
