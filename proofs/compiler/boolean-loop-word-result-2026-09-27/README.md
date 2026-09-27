# Word results from Boolean loops

Candidate `2fdbb81fefff077d192a9341fc3af1a5583fd786` adds a final word-result extraction path for Boolean
loop values bound to pure word continuations, and direct Bool.toUInt64 conversion.
The path preserves exact input/output annotations and standard Id wrappers.
Its independent source semantics and public compiler case extend the instruction,
byte encoding, validation and exported-invocation proofs using the existing loop backend.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 633 inputs across 29 declarations, including twenty-four ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 97,032 native/IR comparisons, 46,080 invalid-input checks and 4,608 controls.
- Prior tests pass 80,640 comparisons, 42,624 invalid-input checks and 2,304 controls.
- The full native corpus contains 1317 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks, including the unchanged
rangeLetBool fixture moved from exclusion to positive coverage. Production and
proof sources are unchanged since the passing proof gate at `3434bd59`. Validation uses
pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.
Pure bindings and local helper declarations around the new word path, multiple
loops, broader helper/proposition bodies and full-dialect correctness remain open.
