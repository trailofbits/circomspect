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
The preparation script builds it with Rust 1.98.1, separately from the analyzer toolchain.

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
The category baseline is retained for regression history. The production and
operator matrix below expands its syntax coverage. It is not an exhaustive
semantic test suite. Incomplete libraries also have analyzer-specific fixtures
under `cli/tests`; missing `main` is classified separately from syntax here.

## Production and operator matrix

`production_matrix.json` expands the category baseline into 141 rows traced to
[`parser/src/lang.lalrpop` at the pinned commit](https://github.com/iden3/circom/blob/ad44e915a12bb047b05745c2884aad9cc8326bc6/parser/src/lang.lalrpop).
Each row names an upstream production or operator, its earliest documented
release, an accepted-syntax case, a token-valid malformed counterpart, the
kind of source construct, and the UTF-8 byte span of the focal syntax. The
separate `grammar_inventory.json` lists the expected row IDs and names the
upstream recovery or invalid-source branches omitted from the valid-source
matrix. The ordinary test checks exact inventory agreement and fixture spans;
the compiler test also checks the operator and assignment token sets against
the pinned grammar text. A fixture with a compiler semantic error still counts
as syntax accepted. The `project_error` result for a definition-only library
records `P1001` (missing main), which is a project requirement rather than a
syntax error: the upstream `ParseAst` production makes `main` optional.

The 319 compiler cases include 139 new accepted/malformed matrix pairs, the
original 18 feature pairs (two also appear in the matrix), one semantic
control, and four compiler-boundary cases. Prefix `++x` and `--x` are grammar
recovery alternatives that produce `P1012`; they are rejected-source cases,
not valid-source production rows. The upstream HEXNUMBER regular expression
matches `0x`, but its action panics while converting an empty digit sequence.
That case is recorded as `compiler_panic` with indeterminate syntax status; it
must not be treated as an ordinary parser rejection or semantic error.

The operator rows cover each token from the upstream unary and infix tables,
and separate fixtures exercise precedence boundaries, left-associative
subtraction, power associativity, and the restricted ternary-arm grammar.
The statement rows include both `for` initializers, dangling `else`, empty and
nonempty `log`, equality constraints, reverse assignments, all twelve compound
assignments, and the invalid prefix forms. The declaration rows cover both
signal orders, bus header orders with and without arguments, tags, arrays,
tuple initialization, and both omitted-parentheses definition forms. The
2.2.3 inline-array cases contain buses and anonymous components.

The matrix asserts source spans and compiler syntax classes. The owned
frontend test additionally checks typed AST variants, operators, declaration
details, and nested expression or statement shape for every row. The
compiler's parser also reports
some errors by semantic or project-level checks, so the recorded class should
not be inferred solely from its exit status or a `P` code prefix.

The `min_version` field means the first known Circom compiler release that
supports a feature. It does not require the source pragma to equal that
release. `old_pragma_bus_success` uses `pragma circom 2.1.0` with a 2.2.0 bus
under compiler 2.2.3 and succeeds: the pragma is a minimum compiler version
request, not a syntax-version lock. The parser version policy must follow this
observed behavior.
