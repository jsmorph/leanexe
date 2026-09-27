# Binary Boolean helpers around word-result loops

Candidate `0a51449d56f5f7f98f06c3e7ad98408cabe0e9d1` admits UInt64-to-UInt64-to-Bool helper declarations
around whole word-result loop computations. Calls may appear in loop bounds,
initial values, step bodies, early exits and final scalar results. Source
semantics and compiled closures preserve captures across every loop state.
Unsupported unused bodies are rejected even when the range is empty.

- Complete source-to-WASM proofs pass 3,397 targets and all 45 audits.
- Native Lean/V8 agree on 2,171 inputs across 106 declarations, including 70 ranges.
- 98 prior modules retain identical bytes; 0 changed.
- New tests pass 9,408 comparisons, 17,664 invalid-input checks and 384 admission controls.
- Prior tests pass 27,264 comparisons, 45,600 invalid-input checks and 672 controls.
- All six fixed probes now compile.
- The native corpus contains 1,715 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) records proof and test development.
Binary predicates around Boolean-result loops and full-dialect compiler
correctness remain open.
