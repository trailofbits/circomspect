# Circomspect 🔎

![Crates.io badge](https://img.shields.io/crates/v/circomspect.svg) ![GitHub badge](https://github.com/trailofbits/circomspect/actions/workflows/ci.yml/badge.svg)

Circomspect is a static analyzer and linter for the [Circom](https://iden3.io/circom)
programming language. It has its own recovering parser and typed semantic representation
for Circom 2.2.3. The Circom compiler is used as a development test oracle, not a runtime
dependency.

Circomspect analyzes functions, templates, and their call contexts using a shared abstract
interpretation engine. It reports properties supported by certified facts and identifies
incomplete analysis separately.

![Circomspect example image](https://github.com/trailofbits/circomspect/raw/main/doc/circomspect.png)

## Installing Circomspect

Circomspect is available on [crates.io](https://crates.io/crates/circomspect) and can be installed by invoking

```sh
  cargo install circomspect
```

To build Circomspect from source, simply clone the repository and build the
project by running `cargo build` in the project root. To install from source, use

```sh
  cargo install --path cli
```

## Running Circomspect

To run Circomspect on a file or directory, simply run

```sh
  circomspect path/to/circuit
```

By default, Circomspect outputs warnings and errors to stdout. To see informational results as well you can set the output level using the `--level` option. To ignore certain types of results, you can use the `--allow` option together with the corresponding result ID. (The result ID can be obtained by passing the `--verbose` flag to Circomspect.)

To output the results to a Sarif file (which can be read by the [VSCode Sarif Viewer](https://marketplace.visualstudio.com/items?itemName=MS-SarifVSCode.sarif-viewer)), use the option `--sarif-file`.

![VSCode example image](https://github.com/trailofbits/circomspect/raw/main/doc/vscode.png)

Circomspect supports the same curves that Circom does: BN254, BLS12-381, and Goldilocks. If you are using a different curve than the default (BN254) you can set the curve using the command line option `--curve`.

Libraries do not need a `main` component. Input directories are searched
recursively for `.circom` files. Use `-L path/to/library` to resolve includes;
the path may name a directory or an individual library file. Results from
included files are hidden unless the file is also an input; errors remain
visible.

Pass each imported package's file or directory with its own `-L`. Package
prefixes in include paths are matched against those roots; ambiguous matches
are reported. Separate input files may each declare a `main` component.
`--timeout SECONDS` gives each template or function call context a positive
wall-clock limit. When a context times out, Circomspect reports `T3002`,
discards findings from that context, and continues with other contexts.
Timeout warnings have no source location and are counted separately from
findings in the final summary.
Source loading, parsing, and project indexing are outside this limit.
The deadline is checked cooperatively during each context's analysis.
Without the option, analysis has no wall-clock limit.

The analyzer recovers from source errors where possible and continues through
independent definitions. Actionable `CS0020` notices name the affected checks,
identify missing parameter values, and suggest analyzing a concrete caller. These
notices are informational (`-l INFO`) and hidden by default. Generic resource-limit
and unsupported-analysis notices are omitted; source errors remain visible.
Repeated findings at the same source location are grouped. Proof locations remain,
and relevant parameter values identify the affected call without an ancestry trace.
No visible reports and no timed-out analyses means exit status 0. Any
visible warning, informational result, error, or timeout means exit status 1.

Source errors and findings appear as analysis progresses. Each finding is printed
once; at `-l INFO`, useful call contexts discovered later appear in an additional
note.
Coverage notices wait until their affected checks have been collected. The final
summary and SARIF file contain the complete grouped results.

Bus declarations are parsed and resolved, but bus and custom-template analysis
contexts remain unsupported. Silence about an unsupported construct is not a proof
that its properties were checked.

Development uses Rust 1.99.0; the tested minimum supported Rust version is 1.74.
Run `cargo test --workspace --locked`, `cargo clippy --all-targets --all-features -- -D warnings`,
and `cargo fmt --all -- --check` from the project root. Dependency checks use
`cargo deny --workspace --all-features --locked check --deny warnings`.
Compiler comparison tests require the pinned compiler described in `tests/conformance`.

## Analysis Passes

Circomspect implements analysis passes for a number of different types of issues. A complete list, together with a high-level description of each issue, can be found [here](https://github.com/trailofbits/circomspect/blob/main/doc/analysis_passes.md).
