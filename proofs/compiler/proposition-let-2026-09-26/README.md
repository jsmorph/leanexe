# Let bindings inside propositions

Candidate `9c05f85fa381151c7e1c88056749eeb0d1011cec` admits Bool and UInt64 lets inside propositions, including
nested bindings, captures, shadowing, unused values and standard Id annotations.
Each condition operand retains its original let scope. Standard leaf decision
evidence contains the checked substitution of each binding's value.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 24,372 native/IR comparisons, 16,152 invalid-input checks and 576 controls.
- Prior tests pass 78,964 comparisons, 47,817 invalid-input checks and 1,792 controls.
- The full native corpus contains 1016 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) and logs preserve proof failures, test corrections and
the outstanding decision type-argument reduction case. Validation uses pinned
Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Let reduction in enclosing decision type arguments, standalone negation of local
Boolean propositions, broader annotations and full-dialect compiler correctness
remain subsequent work.
