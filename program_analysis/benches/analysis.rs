//! End-to-end analysis workloads that exercise the expensive dataflow paths.
// Benchmarks must stop if fixture setup or analysis fails; these failures are not measurements.
#![allow(clippy::allow_attributes, clippy::expect_used)]

use std::hint::black_box;
use std::time::Duration;

use circomspect_program_analysis::application::analyze_files;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use program_structure::constants::Curve;

mod support;

fn analysis(c: &mut Criterion) {
    let fixtures = support::fixture_paths();
    let mut group = c.benchmark_group("analysis");
    group.sample_size(10);
    group.measurement_time(Duration::from_secs(20));
    for (name, path) in fixtures {
        group.bench_with_input(BenchmarkId::from_parameter(name), &path, |b, path| {
            b.iter(|| {
                let result = analyze_files(std::slice::from_ref(path), &[], Curve::Bn254)
                    .expect("analyze benchmark circuit");
                black_box(result);
            });
        });
    }
    group.finish();
}

criterion_group!(benches, analysis);
criterion_main!(benches);
