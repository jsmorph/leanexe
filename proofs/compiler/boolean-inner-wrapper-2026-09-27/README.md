# Standard wrappers around Boolean helper scopes

Candidate `5b4d8a20f6e8c3c2fbceabd17a4b4900c07528db` admits exact Id.run, pure and metadata wrappers around
recursively supported Boolean expressions. Wrappers may nest and may surround
local helpers with repeated calls. The parser checks wrapper types, universes
and the canonical pure instance. Body validation includes unused helper bodies.
Ordinary and dependent conditions and loop exits share the checked conversion.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 993 inputs across 54 declarations, including 25 ranges.
- 44 prior modules retain identical bytes; 0 changed.
- New tests pass 12,724 value/exit comparisons, 11,264 invalid-input checks and 256 controls.
- Prior tests pass 44,308 comparisons, 24,416 invalid-input checks and 3,360 controls.
- All five original wrapper probes pass unchanged.
- The full native corpus contains 1427 declarations.

[verification.json](verification.json) records commands, source/module hashes and
prior module comparisons. The [journal](journal.md) explains the proof and retained
diagnostics. General Boolean composition around helper scopes, broader helper
bodies and inputs, multiple loops, retained instances, broader signatures and
full-dialect compiler correctness remain open.
