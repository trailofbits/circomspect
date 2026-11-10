# CLI and SARIF output contracts

`cli_golden.rs` compares exit codes, terminal output, and full SARIF documents
for libraries without `main`, recovered definitions, missing includes and
callees, malformed input, unsupported versions, locationless errors, secondary
locations, rule suppression, and severity filtering. Only absolute fixture
paths and the temporary SARIF output path are normalized before comparison.
Terminal analysis logs, diagnostics, SARIF results, and rule descriptors are
compared in their emitted order. The SARIF comparison includes rule IDs,
locations, levels, messages, column units, and tool metadata.

The cases in `cli_golden.rs::CASES` exercise these contracts:

- Syntax and missing-call messages use typed frontend diagnostics. Missing-call
  labels select the target name; recovered statements retain their source span.
- Incomplete source and analysis scopes emit `CS0020`, with exact call-path
  locations and all affected rule IDs. Identical typed reasons at an identical
  span share one label. Independent valid definitions continue to be analyzed.
- Generated incidence alone does not certify a redundant quadratic equation.
  The secondary-location fixture checks scoped incomplete analysis in this case.
- An uninstantiated output without a local constraint occurrence is not enough
  to establish an unconstrained-output warning.
- Unsupported-version diagnostics have pragma locations. An absent-input fixture
  covers locationless errors.
- SARIF declares Unicode-code-point columns and distinct per-result location
  IDs. File URIs preserve and encode source file names.

`cutover.rs` separately checks that unused bus and custom-template declarations
cannot silently produce a complete result. Bus definitions retain syntax and
semantic diagnostics and emit scoped `CS0020` for unsupported analysis contexts.

The snapshots test presentation, not warning truth. Frozen truth labels and
historical observations remain in `tests/warnings`.

Update a golden only after reviewing the before/after CLI and SARIF behavior
and explaining the reason in the change review.
