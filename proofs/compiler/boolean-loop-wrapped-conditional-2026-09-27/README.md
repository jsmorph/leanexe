# Wrappers around conditional local Boolean loop calls

Candidate `20d800dc64c1f691c216c44a100c48c638fa7804` admits nested standard Id.run, pure and metadata wrappers
and saved-result lets around conditionals that call local Boolean loop helpers.
The syntax view retains exact wrappers and bindings while exposing the condition
and branches for the existing loop-plan choice proof.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 97,008 native/IR comparisons, 59,904 invalid-input checks and 2,304 binding controls.
- Prior tests pass 193,536 comparisons, 122,112 invalid-input checks and 5,760 controls.
- The full native corpus contains 1296 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks. Validation uses
pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.
General Boolean loop-result bindings, broader helper/proposition bodies and
full-dialect compiler correctness remain open.
