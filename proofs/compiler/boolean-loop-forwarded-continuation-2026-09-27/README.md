# Id binds forwarding to local Boolean loop functions

Candidate `e118d2e58178a7061cef2c2184765b6b25140d40` admits standard Id binds that pass a word or Boolean
action's result directly to a local Boolean-result loop function. Exact input,
output, domain and instance checks preserve the input kind and captured action
references. Standard wrappers around the bind remain supported.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 32,496 native/IR comparisons, 23,040 invalid-input checks and 1,152 binding controls.
- Prior tests pass 97,008 comparisons, 55,296 invalid-input checks and 3,456 controls.
- The full native corpus contains 1266 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks, including the saved
failure for a result binding introduced by show. Validation uses pinned Lean
4.34.0-rc2, Node 24.13.0 and the authorized serial local runner. Conditional
forwarding, saved-result bindings, broader helper/proposition bodies and
full-dialect compiler correctness remain open.
