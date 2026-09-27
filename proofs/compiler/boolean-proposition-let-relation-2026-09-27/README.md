# Boolean relations under proposition lets

Candidate `e3552eb1d60865fd76da1decfe6802fb68de6aef` admits Bool Eq/Ne propositions directly inside retained
Bool/UInt64 lets. Binding types, condition syntax and substituted standard
decisions are checked. Nested lets, captures, Id annotations, unused bindings,
compound guards and ordinary/dependent word or Boolean results are supported.
The structural termination proof accounts for the checked result annotation at
conditional callers. Runtime evaluation reuses the existing guard lowering.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 729 inputs across 38 declarations, including 21 ranges.
- All 28 prior modules retain identical bytes.
- Focused tests pass 80,820 native/IR comparisons, 55,320 invalid-input checks and 1,152 controls.
- Both original rejection fixtures are admitted unchanged.
- Prior tests pass 137,604 comparisons, 77,736 invalid-input checks and 2,528 controls.
- The full native corpus contains 1407 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records the size-bound proof and retained failed
attempts. Checks use pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial
local runner. General helper compositions inside Boolean operands, multiple
loops, retained instances, broader signatures and full-dialect compiler
correctness remain open.
