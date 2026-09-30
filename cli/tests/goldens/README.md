# Current CLI and SARIF output baseline

`cli_golden.rs` compares exit codes, terminal output, and full SARIF documents
for libraries without `main`, recovered definitions, missing includes and
callees, malformed input, locationless errors, secondary locations, rule
suppression, and severity filtering. Absolute fixture paths and the temporary SARIF output path are
normalized before comparison. The SARIF comparison includes result order,
rule IDs, locations, levels, messages, and tool metadata.

The legacy runner iterates definitions through a hash map. Its informational
`analyzing template` lines have no stable order, so the test sorts only those
lines before comparing. Diagnostic order remains exact. This known ordering
gap should be fixed at the runtime cutover and then the normalization removed.
The snapshots record current behavior, including existing bugs; they do not
assert that a reported warning is correct. Warning truth labels live in
`tests/warnings`.

Update a golden only after reviewing the before/after CLI and SARIF behavior
and explaining the reason in the change review.
