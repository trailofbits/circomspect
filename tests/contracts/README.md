# Diagnostic presentation contracts

`active.json` is executed by `cli/tests/cutover.rs` against the application CLI.
It fixes the IDs, SARIF severity, locations, filters, and exit status for
incomplete analysis (`CS0020`) and redundant witness assignments (`CS0021`).
An unresolved global call in a mainless library is incomplete context; it is
visible at info level and does not become a source error.

The redundant-witness fixture also has incomplete field arithmetic and
zero-incidence analysis: its input value is unknown and its witness target
occurs in a generated equation. A proof of one rule does not close the other
analyses. Its expected output therefore includes one scoped `CS0020` beside
`CS0021`. Suppressing `CS0021` alone retains the warning and failure exit;
suppressing both IDs produces a successful empty result. This explicitly
replaces the earlier pending expectation that only `CS0021` would be visible.
