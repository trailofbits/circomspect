use wasm_bindgen::prelude::*;
use wasm_bindgen::JsCast;
use js_sys::{Array, JsString};
extern crate console_error_panic_hook;

use program_analysis::analysis_runner::AnalysisRunner;
use program_structure::constants::Curve;
use program_structure::writers::{CachedStdoutWriter};

#[wasm_bindgen]
pub fn analyze_code(file_content: &JsValue, curve: String) -> String {
    console_error_panic_hook::set_once();

    // Convert incoming JS array or strings to &[&str} for input to analysis_runner
    let array = Array::from(file_content);
    let vec_of_strings: Vec<String> = array.iter()
        .filter_map(|val| val.dyn_into::<JsString>().ok())  // Convert JsValue to JsString
        .map(|js_str| js_str.as_string())  // Convert JsString to String
        .filter_map(|opt| opt)             // Filter out None values (if any)
        .collect();
    let slice_of_strs: Vec<&str> = vec_of_strings.iter().map(|s| s.as_str()).collect();
    let slice: &[&str] = &slice_of_strs;

    let curve = match curve.as_str() {
        "BN254" => Curve::Bn254,
        "BLS12_381" => Curve::Bls12_381,
        "GOLDILOCKS" => Curve::Goldilocks,
        _ => Curve::Bn254,
    };

    // Set up analysis runner, passing the file contents directly
    let (mut runner, sugar_reports) = AnalysisRunner::new(curve)
        .with_src_desugar(&slice);
    let mut stdout_writer = CachedStdoutWriter::new(true);

    // Analyze functions and templates in user provided input files.
    runner.analyze_functions(&mut stdout_writer, true);
    runner.analyze_templates(&mut stdout_writer, true);

    let json_analysis = serde_json::to_string(&stdout_writer.reports()).unwrap();
    let json_sugar_removal_errors = serde_json::to_string(&sugar_reports).unwrap();
    let result = format!("[{},{}]", json_analysis, json_sugar_removal_errors);

    result
}

