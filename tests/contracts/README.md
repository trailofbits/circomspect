# Pending diagnostic presentation contracts

`pending.json` records the future CLI and SARIF behavior for incomplete
analysis (`CS0020`) and exact redundant witness assignment (`CS0021`). These
diagnostics are not emitted by the current runtime. The active test validates
the metadata and source paths; it does not claim the future output already
works. Phase 7 must activate the cases as executable CLI/SARIF assertions
when the new rule pipeline is connected. The table covers default output,
`--level error`, and `--allow` for each diagnostic, with expected exit codes,
rule IDs, SARIF levels, and source scopes.
