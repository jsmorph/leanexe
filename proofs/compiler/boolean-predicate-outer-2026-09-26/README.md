# Boolean-input predicates declared before loops

Candidate `27baeade25dea8ca79fd28e62af5060c08e7a6ab` admits reusable Bool-to-Bool helper declarations
before a loop. Converted calls retain typed arguments and captured values in
bounds, initial values, loop steps, stride calculations and final results.

- The general source-to-WASM theorem and all eighteen axiom audits pass.
- Native Lean/V8 agree on 1,441 inputs across 76 declarations, including 39 ranges.
- All 68 previous modules retain identical bytes.
- Focused tests pass 3,648 native/IR comparisons and 2,304 invalid-input checks.
- Prior tests pass 5,520 comparisons and 3,168 invalid-input checks.
- The full native corpus contains 794 declarations.

[verification.json](verification.json) records commands, source and module hashes.
The [journal](journal.md) records the proof work. Validation uses pinned Lean
4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Calls currently require Bool.toUInt64. Negation and compound Boolean operations
around these calls, direct Boolean-context calls and full dialect compiler
correctness remain subsequent work.
