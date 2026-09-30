# Warning precision corpus

`manifest.json` labels 45 source cases: one `emit`, one `no_finding`, and one
`abstain` for each of 15 rule contracts. `emit` means the narrow property in
the case's `reason` field is present; it does not by itself prove an exploit.
`no_finding` is a near miss for that property, not a declaration
that the whole circuit is safe. `abstain` contains unknown or damaged evidence.
The detailed phase plan is local and ignored; the `reason` field and source
files remain available in a clean checkout.

The active test reruns the current CLI and checks `legacy_observed_count` for
each case. Its baseline is 8 true positives, 3 false positives, 7 false
negatives, 12 true negatives, and 15 cases where the future rule must abstain.
These counts concern the claimed property of the individual rule, using the
rule ID in `legacy_rule_id`. They are not a measure of whole-program safety.
`CS0021` is a planned replacement for the broader current `CS0013` claim;
the corpus records that mapping explicitly. `CS0004` currently covers both
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
holds separate pending CLI/SARIF checks for diagnostics implemented later.
