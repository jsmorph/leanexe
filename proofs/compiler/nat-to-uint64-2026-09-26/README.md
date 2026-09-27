# Nat.toUInt64 for literals and loop indices

Candidate `2bb52ee9bb0cc38bdbf21a31c84aec8fcbb02c28` admits Nat.toUInt64, including the source spelling
i.toUInt64, for checked natural literals and typed loop indices. Conversion
preserves UInt64.ofNat semantics, including modulo 2^64 for large literals.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 180 native/IR comparisons, 728 invalid-input checks and 176 admission/encoding controls.
- Prior tests pass 24,976 comparisons, 9,225 invalid-input checks and 1,026 controls.
- The full native corpus contains 946 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof work and fixture corrections. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Boolean lets/binds inside converted results, broader annotations and full-dialect
compiler correctness remain subsequent work.
