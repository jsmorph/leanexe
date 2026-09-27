# Boolean loop-result bindings

Candidate `b40320d63d192fdfa8fb20be55d537a29764c7c9` admits ordinary lets and standard Id binds that use a
Boolean loop result in a further scalar Boolean expression. The previous
scalar-value/loop-body candidate keeps priority; a whole-path fallback binds the
loop result to the checked continuation and preserves the loop plan's other fields.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 64,752 native/IR comparisons, 34,560 invalid-input checks and 2,304 binding controls.
- Prior tests pass 120,960 comparisons, 84,096 invalid-input checks and 5,760 controls.
- The full native corpus contains 1306 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks, including a corrected
scope assumption in a test control. Validation uses pinned Lean 4.34.0-rc2,
Node 24.13.0 and the authorized serial local runner.
Word results from Boolean loops, multiple-loop composition, broader helper and
proposition bodies and full-dialect compiler correctness remain open.
