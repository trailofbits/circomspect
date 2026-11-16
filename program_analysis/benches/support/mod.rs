//! Fixed Circom workloads shared by time and memory benchmarks.
// Fixture setup must stop a benchmark when it fails rather than produce a measurement.
#![allow(clippy::allow_attributes, clippy::expect_used)]

use std::fmt::Write;
use std::fs;
use std::path::PathBuf;

pub(crate) fn fixture_paths() -> [(&'static str, PathBuf); 4] {
    [
        ("array_writes", fixture("array_writes", &table_source(2_048))),
        ("array_writes_large", fixture("array_writes_large", &table_source(16_384))),
        ("equations", fixture("equations", &constraints_source(256))),
        ("output_elements", fixture("output_elements", &outputs_source(128))),
    ]
}

fn fixture(name: &str, source: &str) -> PathBuf {
    let directory = std::env::temp_dir().join(format!("circomspect-bench-{}", std::process::id()));
    fs::create_dir_all(&directory).expect("create benchmark directory");
    let path = directory.join(format!("{name}.circom"));
    fs::write(&path, source).expect("write benchmark circuit");
    path
}

fn table_source(size: usize) -> String {
    let mut source = String::from("pragma circom 2.2.3;\nfunction Table() {\nvar powers[");
    source.push_str(&size.to_string());
    source.push_str("];\n");
    for index in 0..size {
        writeln!(source, "powers[{index}] = {index};").expect("write to String");
    }
    write!(source, "return powers[{}];\n}}\n", size - 1).expect("write to String");
    source
}

fn constraints_source(size: usize) -> String {
    let mut source = format!(
        "pragma circom 2.2.3;\ntemplate Dense() {{\nsignal input in;\n\
         signal output out;\nsignal a[{size}];\na[0] <== in;\n"
    );
    for index in 1..size {
        writeln!(source, "a[{index}] <== a[{}] + 1;", index - 1).expect("write to String");
    }
    write!(source, "out <== a[{}];\n}}\n", size - 1).expect("write to String");
    source
}

fn outputs_source(size: usize) -> String {
    let mut source = format!(
        "pragma circom 2.2.3;\ntemplate Outputs() {{\nsignal input in;\n\
         signal output out[{size}];\n"
    );
    for index in 0..size {
        writeln!(source, "out[{index}] <== in + {index};").expect("write to String");
    }
    source.push_str("}\n");
    source
}
