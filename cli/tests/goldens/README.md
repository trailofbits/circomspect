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
- Actionable analysis limitations emit `CS0020`, with affected check names,
  rule IDs, source locations and help. Missing context is informational and hidden
  by default. Vague causes and redundant notices for source errors are omitted.
  Independent valid definitions continue to be analyzed.
- Generated incidence alone does not certify a redundant quadratic equation.
  The secondary-location fixture checks the resulting output without treating
  a missing proof as a circuit defect.
- An uninstantiated output without a local constraint occurrence is not enough
  to establish an unconstrained-output warning.
- Unsupported-version diagnostics have pragma locations. An absent-input fixture
  covers locationless errors.
- SARIF declares Unicode-code-point columns and distinct per-result location
  IDs. File URIs preserve and encode source file names.

`cutover.rs` separately checks that unused bus and custom-template declarations
cannot silently produce a complete result. Bus definitions retain syntax and
semantic diagnostics and emit scoped `CS0020` for unsupported analysis contexts.
It also checks default/INFO filtering, suppression of nonactionable notices,
grouped unused-value and curve findings, and retained call-path locations.
The summary separates findings, source errors and analysis notices; hidden
informational reports contribute neither a count nor an exit failure.

The snapshots test presentation, not warning truth. Frozen truth labels and
historical observations remain in `tests/warnings`.

Terminal snapshots place frontend diagnostics before definition analysis. Findings
arrive after each completed context; final call-path continuations do not repeat
or count the warning. SARIF retains deterministic source order and complete
evidence. `live_output::tests` blocks a later scope to verify actual pipe delivery.

Update a golden only after reviewing the before/after CLI and SARIF behavior
and explaining the reason in the change review.
