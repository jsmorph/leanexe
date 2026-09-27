# Boolean parameters in scalar functions

Candidate `6fd287e75aa9ea777f756277311097951d2de50e` admits mixed UInt64/Bool public parameters for scalar
bodies. Every exported i64 input is covered: zero decodes to false and every
nonzero Boolean input decodes to true. Compiled Boolean bindings normalize to
zero/one; word inputs retain their bits. Source application and extraction check
lambda annotations against the declared parameter types.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 439 inputs across 28 declarations, including six prior ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 44,492 native/IR comparisons, 18,432 invalid-input checks and 1,056 controls.
- Prior tests pass 126,334 comparisons, 87,375 invalid-input checks and 4,992 controls.
- The full native corpus contains 1086 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) preserves proof failures and capture diagnostics. The
original native fixture draft and diagnostic source record unsupported combinations
for subsequent grammar work; the `scalar_public_boolean_parameters` files are the
completed tests for this increment.

Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Boolean inputs in loops, Boolean loop results, broader helper/proposition
bodies, parameter annotations and full-dialect correctness remain subsequent work.
