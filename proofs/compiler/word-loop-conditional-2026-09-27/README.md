# Word-result conditionals over scalar and loop computations

Candidate `800c72b7ef9dea831c8ece6c6ee7279a8d63605c` admits nested UInt64-result choices among scalar
expressions, word loops and Boolean-derived word computations. Both branches
are checked; source execution follows the selected branch. Standard Id result
annotations and run/pure/metadata wrappers preserve the selected computation.
The general word layer reuses the proved component grammars and loop plan.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 258,288 native/IR comparisons, 129,024 invalid-input checks and 9,216 controls.
- Prior tests pass 306,432 comparisons, 154,368 invalid-input checks and 18,432 controls.
- The full native corpus contains 1347 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks and retained failures.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Setup/helpers around these word conditionals, multiple loops, broader
helper/proposition bodies and full-dialect correctness remain open.
