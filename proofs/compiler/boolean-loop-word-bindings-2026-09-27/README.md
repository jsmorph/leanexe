# Bindings around Boolean-to-word loops

Candidate `2c1781f9f7a13041a9ae1d37111da5e7d5d021c0` admits pure word and Boolean setup before Boolean-to-word
loops, and saved word results used by further pure expressions. Both ordinary
lets and exact standard Id binds retain their annotations. Existing Boolean
loop-result candidates keep priority. Shared binding combinators have explicit
acceptance and success proofs for both candidate orders.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 129,264 native/IR comparisons, 76,800 invalid-input checks and 6,144 controls.
- Prior tests pass 161,280 comparisons, 80,640 invalid-input checks and 6,912 controls.
- The full native corpus contains 1327 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks, including the explicit
Id.run operands needed by an annotated native fixture. Validation uses pinned
Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.
Local helper declarations around this word path, broader outer word conditionals,
multiple loops, broader helper/proposition bodies and full-dialect correctness remain open.
