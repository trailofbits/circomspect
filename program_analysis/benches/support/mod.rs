//! Fixed Circom workloads shared by time and memory benchmarks.
// Fixture setup must stop a benchmark when it fails rather than produce a measurement.
#![allow(clippy::allow_attributes, clippy::expect_used)]

use std::fmt::Write;
use std::fs;
use std::path::PathBuf;

pub(crate) fn fixture_paths() -> [(&'static str, PathBuf); 6] {
    [
        ("array_writes", fixture("array_writes", &table_source(2_048))),
        ("array_writes_large", fixture("array_writes_large", &table_source(16_384))),
        ("equations", fixture("equations", &constraints_source(256))),
        ("output_elements", fixture("output_elements", &outputs_source(128))),
        ("new_rules", fixture("new_rules", &new_rules_source())),
        ("alternate_witness", fixture("alternate_witness", witness_alternative_source())),
    ]
}

fn witness_alternative_source() -> &'static str {
    "pragma circom 2.2.3;\n\
     template WitnessAlternative() {\n\
     signal input x; signal output y;\n\
     x === 1; y <-- x; y * (y - x) === 0;\n\
     }\ncomponent main {public [x]} = WitnessAlternative();\n"
}

fn new_rules_source() -> String {
    let mut source = String::from(
        "pragma circom 2.2.3;\ntemplate NewRules() {\n\
         signal input ignored;\nsignal input x;\nsignal input bits[254];\n\
         signal output y;\nsignal output packed;\nsignal output inverse;\n\
         signal output {binary} tagged;\n\
         y <-- x;\ny * (y - x) === 0;\n\
         inverse <-- 1 / x;\nx * (x - 1) === 0;\ninverse * x === x;\n\
         tagged <== x + bits[0];\nvar accumulator = 0;\n",
    );
    source.push_str(
        "for (var i = 0; i < 254; i++) {\n\
         bits[i] * (bits[i] - 1) === 0;\naccumulator += bits[i] * (2 ** i);\n}\n\
         packed <== accumulator;\n}\n\
         component main {public [ignored, x]} = NewRules();\n",
    );
    source
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
