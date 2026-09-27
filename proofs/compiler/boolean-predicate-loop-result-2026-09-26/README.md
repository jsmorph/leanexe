# Direct Boolean helper results across loop scopes

Candidate `3c4dbc3e6d85ddb45504fef0f4b9c00e53227628` admits UInt64-to-Bool and Bool-to-Bool helper bodies
returning supported Boolean calls directly in loop-step and outer-loop declarations.
Chained helpers, captures, wrappers, negation and unused declarations are checked.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 521 inputs across 26 declarations, including seventeen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 24,768 native/IR comparisons, 9,216 invalid-input checks and 1,024 controls.
- Prior tests pass 18,580 comparisons, 11,792 invalid-input checks and 720 controls.
- The full native corpus contains 936 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof work, fixture corrections and the discovered
Nat.toUInt64 gap. Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the
authorized serial local runner.

Nat.toUInt64, Boolean lets/binds inside converted results, broader annotations and
full-dialect compiler correctness remain subsequent work.
