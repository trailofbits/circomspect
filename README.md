# Circomspect 🔎

![Crates.io badge](https://img.shields.io/crates/v/circomspect.svg) ![GitHub badge](https://github.com/trailofbits/circomspect/actions/workflows/ci.yml/badge.svg)

Circomspect is a static analyzer and linter for the [Circom](https://iden3.io/circom) programming language. The codebase borrows heavily from the Rust Circom compiler built by [iden3](https://github.com/iden3).

Circomspect currently implements a number of analysis passes which can identify potential issues in Circom circuits. It is our goal to continue to add new analysis passes to be able to detect more issues in the future.

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

Circomspect supports the same curves that Circom does: BN128, BLS12-381, and Goldilocks. If you are using a different curve than the default (BN128) you can set the curve using the command line option `--curve`.

## Analysis Passes

Circomspect implements analysis passes for a number of different types of issues. A complete list, together with a high-level description of each issue, can be found [here](doc/analysis_passes.md).
