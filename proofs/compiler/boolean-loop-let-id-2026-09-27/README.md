# Id annotations on Boolean-loop let bindings

Candidate `85ec28a20155e5bc040b7a20a7a70918b3433e2e` admits any number of standard Id layers on let domains
for word setup, Boolean setup and word-loop results in Boolean-returning functions.
The source semantics retain the annotations. Exact Id heads and universes are
checked, and the underlying binding's type and body remain checked.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 64,752 native/IR comparisons, 78,336 invalid-input checks and 6,912 controls.
- Prior tests pass 185,952 comparisons, 137,472 invalid-input checks and 11,712 controls.
- The full native corpus contains 1156 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records the proof and execution checks. Validation uses
pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner. Outer
local helpers and loop-containing continuations, broader helper/proposition
bodies and full-dialect compiler correctness remain open.
