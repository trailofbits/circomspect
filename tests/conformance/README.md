# Circom 2.2.3 compiler corpus

This corpus pins the official [`iden3/circom` v2.2.3 commit](https://github.com/iden3/circom/tree/ad44e915a12bb047b05745c2884aad9cc8326bc6).
Build it and run the comparison from the repository root:

```sh
bash tests/conformance/prepare_compiler.sh /tmp/circomspect-oracle
CIRCOM_COMPILER=/tmp/circomspect-oracle/circom-v2.2.3/target/release/circom \
  cargo test -p circomspect --test conformance -- --ignored
```

CI runs both commands and fails if the compiler cannot be obtained or a result
differs. The build script verifies the checked-out commit and `--version`.
`manifest.json` records the feature, earliest supported version used by this
corpus, curve, source, accepted/rejected syntax, compiler result class, and
first diagnostic code. Every fixture is a complete program with its own
`main`; the compiler sees its original context. An additional semantic-error
control proves that a type error is not mistaken for a grammar rejection.
The compiler is a development oracle and is not used by Circomspect at runtime.

| Feature | Since | Accepted and rejected cases |
| --- | --- | --- |
| Declarations and assignments | 2.0.0 | `declarations_*` |
| Includes | 2.0.0 | `includes_*` |
| Functions | 2.0.0 | `functions_*` |
| Templates and components | 2.0.0 | `templates_*` |
| Custom templates | 2.0.6 | `custom_templates_*` |
| Buses | 2.2.0 | `buses_*` |
| Tags | 2.1.0 | `tags_*` |
| Arrays and indexing | 2.0.0 | `arrays_*` |
| Tuples | 2.1.0 | `tuples_*` |
| Anonymous components | 2.1.0 | `anonymous_components_*` |
| Inline arrays | 2.1.0 | `inline_arrays_*` |
| `for` loops | 2.0.0 | `loops_*` |
| Operators | 2.0.0 | `operators_*` |
| `input signal` declaration order | 2.2.0 | `declaration_order_*` |
| Inline arrays of buses | 2.2.3 | `inline_array_buses_*` |
| Inline arrays of anonymous components | 2.2.3 | `inline_array_anonymous_*` |
| `while` loops | 2.0.0 | `while_loops_*` |
| Conditionals | 2.0.0 | `conditionals_*` |

The version-specific entries follow the official [release history](https://github.com/iden3/circom/blob/ad44e915a12bb047b05745c2884aad9cc8326bc6/RELEASES.md)
and [language documentation](https://docs.circom.io/circom-language/).
This is a syntax inventory, not an exhaustive semantic test suite. Incomplete
libraries and missing `main` are analyzer-specific fixtures under `cli/tests`:
the compiler requires a main program, so it cannot classify those inputs.
