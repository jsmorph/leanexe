# Equality and decisions over Boolean-input predicate calls

Candidate `6d697071052a607c928dc4654cefea9f575daeee` admits equality and inequality of Bool-to-Bool helper
results, through BEq/bne and decisions of Boolean Eq/Ne propositions. Each operand
retains its Boolean check in scalar, loop-step and outer-loop scopes. Standard
comparison and decision evidence is checked before recursive compilation.

- The general source-to-WASM theorem and all eighteen axiom audits pass.
- Native Lean/V8 agree on 2,161 inputs across 116 declarations, including 55 ranges.
- All 106 previous modules retain identical bytes.
- Focused tests pass 16,052 native/IR comparisons and 11,574 invalid-input checks.
- Twelve positive controls accompany the evidence/type rejection tests.
- Prior tests pass 16,356 comparisons and 11,540 invalid-input checks.
- The full native corpus contains 834 declarations.

[verification.json](verification.json) records commands, source and module hashes.
The [journal](journal.md) records proof work and retained diagnostics. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Boolean choices, direct Boolean contexts and full dialect compiler correctness
remain subsequent work.
