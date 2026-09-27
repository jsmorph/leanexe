# Outer conditions selecting Boolean-result loops

Candidate `a72408e87a51f81d36f570733d7457abee1452a8` admits ordinary if expressions with a Boolean or standard
Id Boolean result and two admitted loop arms. Exact condition evidence and both
arms are checked. The captured condition selects the same loop plan throughout
execution, including its bound, initial value, step, exit flag and final result.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 16,368 native/IR comparisons, 11,520 invalid-input checks and 1,152 wrapper controls.
- Prior tests pass 40,560 comparisons, 39,168 invalid-input checks and 2,880 controls.
- The full native corpus contains 1226 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Mixed scalar/loop arms, loop-containing continuations, broader helper and
proposition bodies, and full-dialect compiler correctness remain open.
