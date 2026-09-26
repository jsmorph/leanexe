# Retained predicate input annotations

Candidate `40b8569c695462cb5f56cefcfcae522704560be6` admits matching standard Id layers on reusable
UInt64-to-Bool helper inputs in scalar, loop-step and outer-loop declarations.
Input and result types, lexical captures and unused bodies are checked.

- The general source-to-WASM theorem and all eighteen axiom audits pass.
- Native Lean/V8 agree on 951 inputs across 51 declarations, including 25 ranges.
- All 41 previous modules retain identical bytes.
- Focused tests pass 9,108 native/IR comparisons and 7,344 invalid-input checks.
- Prior outer-predicate and step-result tests pass 2,112 comparisons and 864
  invalid-input checks. The full native corpus contains 769 declarations.

[verification.json](verification.json) records commands, source and module hashes.
The [journal](journal.md) records proof work and retained diagnostics. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Reusable Bool-to-Bool helpers and full dialect compiler correctness remain
subsequent work.
