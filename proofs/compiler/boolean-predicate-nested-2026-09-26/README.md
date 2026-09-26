# Nested converted Boolean-input predicate calls

Candidate `24655f11372e4b8c9322ff19e2251bc0bfed9480` admits nested Bool-to-Bool helper calls under
Bool.toUInt64, with inner and outer negation. Each argument retains its Boolean
check in scalar, loop-step and outer-loop scopes. The source result lemma proves
that every admitted Boolean conversion evaluates to an encoded Boolean.

- The general source-to-WASM theorem and all eighteen axiom audits pass.
- Native Lean/V8 agree on 1,801 inputs across 96 declarations, including 47 ranges.
- All 86 previous modules retain identical bytes.
- Focused tests pass 12,084 native/IR comparisons and 8,640 invalid-input checks.
- Prior tests pass 12,896 comparisons and 9,360 invalid-input checks.
- The full native corpus contains 814 declarations.

[verification.json](verification.json) records commands, source and module hashes.
The [journal](journal.md) records proof work and retained diagnostics. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Compound calls, direct Boolean-context calls and full dialect compiler
correctness remain subsequent work.
