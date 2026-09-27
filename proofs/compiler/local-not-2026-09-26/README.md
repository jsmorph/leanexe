# Standalone propositional negation of local Boolean values

Candidate `165b83c07716a3ef114cdcb823200de4d0a913d0` admits one or more propositional Not wrappers around
saved flags, local Boolean helper calls and supported compound Boolean values.
Scalar and loop conditions, dependent branches, Boolean-result choices and saved
decisions share the checked source representation and lowering.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 537 inputs across 30 declarations, including thirteen ranges.
- Twenty prior modules retain identical bytes: eighteen from the preceding archive
  and the saved/call negation examples from their original archives.
- Focused tests pass 33,780 native/IR comparisons, 23,040 invalid-input checks and 480 controls.
- Prior tests pass 200,284 comparisons, 114,689 invalid-input checks and 4,704 controls.
- The full native corpus contains 1036 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) and logs preserve proof attempts and validation results.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Retained annotations, broader signatures and full-dialect compiler
correctness remain subsequent work.
