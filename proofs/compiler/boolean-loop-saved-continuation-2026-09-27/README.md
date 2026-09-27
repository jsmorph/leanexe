# Saved results of local Boolean loop calls

Candidate `d6465e8bbdad44a5e52216190e5a462222a747f0` admits saved direct and forwarded local call results
returned by their exact bound variable. It preserves Bool/Id annotations, binder
flags, captured arguments, nested wrappers and shadowed names. The saved show
failure now passes.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 97,008 native/IR comparisons, 76,032 invalid-input checks and 3,456 binding controls.
- Prior tests pass 129,024 comparisons, 69,120 invalid-input checks and 3,456 controls.
- The full native corpus contains 1286 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks. Validation uses
pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.
Wrappers and saved results around conditional calls, broader Boolean loop-result
bindings, helper/proposition bodies and full-dialect compiler correctness remain open.
