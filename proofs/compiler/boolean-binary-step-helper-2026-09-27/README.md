# Binary Boolean helper declarations in word loop steps

Candidate `67e4287bfaf48291ed62e8b55c18d699bd6501b0` admits UInt64-to-UInt64-to-Bool helper declarations
around complete word-accumulator loop steps. Source evaluation, totality,
extraction, complete admission and IR invariants preserve captures, argument order,
saved results and early exits. Unused bodies are checked even in empty ranges.

- Complete source-to-WASM proofs pass 3,396 targets and all 38 audits.
- Native Lean/V8 agree on 1,595 inputs across 82 declarations, including 46 ranges.
- 74 prior modules retain identical bytes; 0 changed.
- New tests pass 9,408 native/IR comparisons, 17,664 invalid-input checks and 384 admission controls.
- Prior tests pass 20,042 comparisons, 29,520 invalid-input checks and 288 admission controls.
- All six fixed probes compile; five already compiled before this extension.
- The native corpus contains 1,691 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) records proof development and tests.
Binary predicates in Boolean-accumulator loop steps and full-dialect correctness
remain open.
