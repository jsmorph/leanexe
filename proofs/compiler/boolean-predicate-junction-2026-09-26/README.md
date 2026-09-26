# Conjunction and disjunction of Boolean-input predicate calls

Candidate `6abc02c628283356980b4ef9a17c4238e0214b2a` admits conjunctions and disjunctions containing
Bool-to-Bool helper calls under Bool.toUInt64, including nested calls and negation.
Each operand retains its Boolean check in scalar, loop-step and outer-loop scopes.
The new lowering composes existing proved word operations; expressions in the
previous source grammar retain their previous lowering.

- The general source-to-WASM theorem and all eighteen axiom audits pass.
- Native Lean/V8 agree on 1,981 inputs across 106 declarations, including 51 ranges.
- All 96 previous modules retain identical bytes.
- Focused tests pass 16,052 native/IR comparisons and 11,520 invalid-input checks.
- Prior tests pass 12,084 comparisons and 8,640 invalid-input checks.
- The full native corpus contains 824 declarations.

[verification.json](verification.json) records commands, source and module hashes.
The [journal](journal.md) records proof work and retained diagnostics. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Boolean equality, choices, direct Boolean contexts and full dialect compiler
correctness remain subsequent work.
