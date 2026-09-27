# Scalar word setup before Boolean loop results

Candidate `4fcf2d6bf5f4d03a165f05f7ac533dbaa2214ee1` admits scalar UInt64 let bindings and word-valued Id
actions before a Boolean loop body. Their lexical values are preserved across
loop states and can supply bounds, initial values, captures and final results.
Both used and unused setup expressions are checked.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 599 inputs across 28 declarations, including twenty-two ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 24,432 native/IR comparisons, 13,824 invalid-input checks and 1,728 lexical setup controls.
- Prior tests pass 153,696 comparisons, 113,280 invalid-input checks and 6,528 controls.
- The full native corpus contains 1136 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) and logs retain failed theorem/test syntax attempts.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Boolean setup and outer helper declarations before Boolean loops, broader
helper/proposition bodies and full-dialect compiler correctness remain open.
