# Id binds inside converted Boolean results

Candidate `937744e9aa191f1304ea3685bd9bef55cd3d543b` admits standard Id binds of Boolean and UInt64 values
inside Boolean results. Nested binds preserve captures, shadowing, negation and
Id annotations. The parser checks the standard instance, exact input and
continuation types, and Boolean result type; unused values are also checked.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 3,764 native/IR comparisons, 3,072 invalid-input checks and 256 controls.
- Prior tests pass 42,768 comparisons, 28,032 invalid-input checks and 2,368 controls.
- The full native corpus contains 976 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof work; build and test logs retain both the
failed parser proof and successful checks. Validation uses pinned Lean 4.34.0-rc2,
Node 24.13.0 and the authorized serial local runner.

Saved Boolean variables in mixed propositional guards, broader annotations and
full-dialect compiler correctness remain subsequent work.
