# Direct calls to local Boolean loop functions

Candidate `ec6ed21bb3306005a5ea99fd2674d18ec106378e` admits direct calls to local functions containing
Boolean-result loops, with word and Boolean parameters. Arguments cannot refer
to the helper itself; outer captures retain their bindings. The existing scalar
helper path is tried before direct continuation extraction.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 16,368 native/IR comparisons, 5,760 invalid-input checks and 576 binding controls.
- Prior tests pass 161,280 comparisons, 96,768 invalid-input checks and 8,064 controls.
- The full native corpus contains 1246 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks, including the saved
failure for an Id.run wrapper around a call. Validation uses pinned Lean
4.34.0-rc2, Node 24.13.0 and the authorized serial local runner. Standard wrappers
and conditional forwarding around local calls, broader helper/proposition
bodies and full-dialect compiler correctness remain open.
