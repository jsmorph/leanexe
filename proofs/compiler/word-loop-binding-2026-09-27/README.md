# Bindings around word-result conditional loops

Candidate `96bc2810a1ba3eb1fa6db108f4a1b677ae2d5568` admits pure word/Boolean setup and saved word results
around conditional loops. Ordinary lets, exact standard Id binds and show retain
annotations and captures. Both used and unused values are checked. A loop value
requires a pure tail, so sequential dynamic loops remain rejected.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 129,264 native/IR comparisons, 73,728 invalid-input checks and 6,144 controls.
- Prior tests pass 387,072 comparisons, 205,824 invalid-input checks and 15,360 controls.
- The full native corpus contains 1357 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks. Validation uses
pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.
Local helpers around word conditionals, multiple loops, broader helper/proposition
bodies and full-dialect correctness remain open.
