# Boolean setup before Boolean loop results

Candidate `0dc8dd04c29eec351ba9dfef48d32abb847c85ff` admits Bool let bindings and standard Boolean-to-Boolean
Id actions before a Boolean loop body. The checked flag conversion gives the
source Boolean value, preserved in loop captures and the final result. Bind
input/output types may retain Id layers, with exact continuation domains and
standard instance evidence. Used and unused setup expressions are checked.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 24,432 native/IR comparisons, 24,192 invalid-input checks and 3,456 lexical/unused setup controls.
- Prior tests pass 161,760 comparisons, 113,280 invalid-input checks and 8,256 controls.
- The full native corpus contains 1146 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) and logs retain the conditional-action fixture that
elaborates to a loop-containing local continuation, an unsupported form. Its
source and elaborated expression are preserved for subsequent coverage.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Id-annotated loop let domains, outer helpers and loop-containing local
continuations, broader helper/proposition bodies and full-dialect compiler
correctness remain open.
