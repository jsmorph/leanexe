# Consecutive bounded word-result loops

Candidate `b60b926a7b119b404e5ac157e6120362fec00014` admits consecutive word-result computations through
ordinary lets and exact standard Id binds. Each loop preserves earlier result
locals and lexical captures. Bounds may depend on earlier results. Early exits,
continue, unused computations, shadowed bindings and retained Id annotations
are covered. Unsupported unused computations reject even in empty ranges.

- Complete source-to-WASM proofs pass 3,413 targets and all 53 audits.
- Native Lean/V8 agree on 2,603 inputs across 124 declarations, including 88 ranges.
- All 114 prior modules retain identical bytes.
- New tests pass 14,016 comparisons, 18,432 invalid-input checks and 576 controls.
- Prior tests pass 18,816 comparisons, 35,328 invalid-input checks and 768 controls.
- Five fixed word probes compile; the sixth Boolean-result probe remains deferred.
- The native corpus contains 1,733 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) records proof and test development, including two old
exclusion tests now admitted unchanged and checked in V8. The proof candidate
is `1ae72835`; subsequent candidate commits change only tests and task status.
Boolean-result sequences, nested loops, broader helper signatures and
full-dialect compiler correctness remain open.
