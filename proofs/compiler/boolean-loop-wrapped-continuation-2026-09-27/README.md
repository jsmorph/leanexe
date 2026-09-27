# Standard wrappers around local Boolean loop calls

Candidate `ebc681ae91eaff0ee9dc01819b519f85adcde829` admits any finite sequence of exact standard Id.run,
pure and metadata wrappers around local calls to Boolean-result loops. Source
call shapes preserve each wrapper and the argument's captured references.
The existing scalar helper path remains first.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 97,008 native/IR comparisons, 55,296 invalid-input checks and 3,456 binding controls.
- Prior tests pass 80,640 comparisons, 61,056 invalid-input checks and 5,184 controls.
- The full native corpus contains 1256 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks. The Id.run failure
saved in the direct-call increment now passes. Validation uses pinned Lean
4.34.0-rc2, Node 24.13.0 and the authorized serial local runner. Id binds and
conditional forwarding around local calls, broader helper/proposition bodies
and full-dialect compiler correctness remain open.
