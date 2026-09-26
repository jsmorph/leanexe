# Negated converted Boolean-input predicate calls

Candidate `038777791a4b6228dd44aca55b381ac5965c6c60` admits any number of Boolean Not wrappers around
a Bool-to-Bool helper call under Bool.toUInt64. Source and compiled bindings
retain Boolean argument checks in scalar, loop-step and outer-loop scopes.
The zero-negation case keeps its existing expression.

- The general source-to-WASM theorem and all eighteen axiom audits pass.
- Native Lean/V8 agree on 1,621 inputs across 86 declarations, including 43 ranges.
- All 76 previous modules retain identical bytes.
- Focused tests pass 4,148 native/IR comparisons and 3,072 invalid-input checks.
- Prior tests pass 1,484 comparisons and 864 invalid-input checks.
- The full native corpus contains 804 declarations.

[verification.json](verification.json) records commands, source and module hashes.
The [journal](journal.md) records proof work and retained diagnostics. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Nested/compound calls, direct Boolean-context calls and full dialect compiler
correctness remain subsequent work.
