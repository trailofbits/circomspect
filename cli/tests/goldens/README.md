# CLI and SARIF output contracts

`cli_golden.rs` compares exit codes, terminal output, and full SARIF documents
for libraries without `main`, recovered definitions, missing includes and
callees, malformed input, unsupported versions, locationless errors, secondary
locations, rule suppression, and severity filtering. Only absolute fixture
paths and the temporary SARIF output path are normalized before comparison.
Terminal analysis logs, diagnostics, SARIF results, and rule descriptors are
compared in their emitted order. The SARIF comparison includes rule IDs,
locations, levels, messages, column units, and tool metadata.

The owned frontend and analysis pipeline intentionally changed these outputs:

- Syntax and missing-call messages use typed frontend diagnostics. Missing-call
  labels select the target name; recovered statements retain their source span.
- Incomplete source and analysis scopes emit `CS0020`, with exact call-path
  locations and all affected rule IDs. Identical typed reasons at an identical
  span share one label. Independent valid definitions continue to be analyzed.
- The secondary-location fixture has generated incidence but no certified
  redundant quadratic equation. Its old `CS0005` warning is replaced by scoped
  incomplete analysis, according to the conservative rule predicates.
- An uninstantiated output in the missing-include library is no longer called
  unconstrained solely because it has no local constraint occurrence.
- The unsupported-version case now requires Circom 2.3.0 because 2.2.0 is
  supported. It has a pragma location. A separate absent-input fixture retains
  coverage for locationless errors, bringing the corpus to ten cases.
- SARIF declares Unicode-code-point columns and distinct per-result location
  IDs. File URIs preserve and encode source file names.
- Bus definitions retain syntax and semantic diagnostics and emit scoped
  `CS0020` because their analysis context is unsupported. Unused bus and
  custom-template declarations cannot silently produce a complete result.

The comparator implementation also adds `CS0014` to the existing incomplete-analysis
labels for both malformed definitions in `partial_library`. The terminal layout,
source locations, diagnostic count, exit code, and other nine cases are unchanged.

The snapshots test presentation, not warning truth. Frozen truth labels and
historical observations remain in `tests/warnings`.

Update a golden only after reviewing the before/after CLI and SARIF behavior
and explaining the reason in the change review.
