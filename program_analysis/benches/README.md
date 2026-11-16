# Analysis benchmarks

Run the end-to-end Circom workloads with:

```sh
cargo bench -p circomspect-program-analysis --bench analysis
```

The benchmark generates four fixed circuits outside the measured loop: two sizes of array-write
table, many distinct constraints, and an output array. Each measurement includes source loading,
HIR and CFG construction, all analysis passes, and reporting. The fixtures are synthetic so
the benchmark does not depend on a separately installed circuit library.

Record a baseline before changing an analysis pass, then compare on the same machine:

```sh
cargo bench -p circomspect-program-analysis --bench analysis -- --save-baseline before
cargo bench -p circomspect-program-analysis --bench analysis -- --baseline before
```

Criterion stores baselines under `target/criterion`. Inspect its reported confidence interval
and percent change; it does not enforce a CI threshold because shared CI runners vary widely.
For a suspected regression, profile the relevant circuit separately and compare the same
checkout, build profile, and input before and after the change.

## Peak memory

The memory benchmark runs the same four circuits in three fresh processes each. It reports the
median peak resident set size (RSS), along with the smallest and largest sample. It supports
macOS and Linux.

```sh
cargo bench -p circomspect-program-analysis --bench memory
cargo bench -p circomspect-program-analysis --bench memory -- --save-baseline memory.json
cargo bench -p circomspect-program-analysis --bench memory -- --baseline memory.json
```

The baseline is a JSON file with the median peak RSS in bytes for each workload. Comparison
fails when any median exceeds its baseline by more than 20%. Run both commands on the same
machine and build profile; the baseline also checks the operating system and architecture.
Peak RSS includes process startup and the Rust runtime, and it is not an allocation count.
Like the timing benchmark, this comparison is intended for local regression checks rather than
an enforced threshold on shared CI runners.
