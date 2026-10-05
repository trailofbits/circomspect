# Warning precision corpus

`manifest.json` labels 45 source cases: one `emit`, one `no_finding`, and one
`abstain` for each of 15 rule contracts. `emit` means the narrow property in
the case's `reason` field is present; it does not by itself prove an exploit.
`no_finding` is a near miss for that property, not a declaration
that the whole circuit is safe. `abstain` contains unknown or damaged evidence.
The detailed phase plan is local and ignored; the `reason` field and source
files remain available in a clean checkout.

The CLI replay checks each target rule within the declared source scope.
An `emit` case must have a finding, a `no_finding` case must not, and an
`abstain` case must have scoped `CS0020` with no target finding. The separate
metadata test preserves historical counts and evidence: 8 true positives,
2 false positives, 7 false negatives, 13 true negatives, and 15 cases requiring
abstention. These counts concern the claimed property of the individual rule,
not whole-program safety. `CS0021` replaces the broader former `CS0013` claim;
the corpus records that mapping explicitly. `CS0004` covers both
bitwise complement and field arithmetic, so the separate `rule` keys keep
their precision cases distinct.

The ignored compiler test checks that every complete warning fixture has the
recorded Circom 2.2.3 success, syntax-error, or semantic-error class. The
uninstantiated library case has `compiler_class: no_main`: the compiler
requires a main, while the analyzer must accept the library as an input.
The compiler run is explicit in CI.

To preserve adjudications, add new cases rather than silently changing a
source or its label. If a case is found to be mislabeled, record the reason in
the change review and update the expected counts deliberately. `tests/contracts`
holds active CLI/SARIF checks for incomplete analysis and redundant witnesses.

To retain per-case messages, source spans, classifications, incomplete scopes,
exit codes, and elapsed CLI time, set `CIRCOMSPECT_CORPUS_REPORT` to an output
path when running `cli_warning_corpus_preserves_adjudicated_findings`. The JSON
report is updated after each case; `complete: true` means all cases ran, while
an empty `failures` list means the replay met its expectations. Evidence reports
belong in the ignored `codex/` directory.
