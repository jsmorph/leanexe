# Binary Boolean helpers around Boolean-result loops

Candidate `41c13c4750828808515bf737bb8ba079babb0774` admits UInt64-to-UInt64-to-Bool helper declarations
around Boolean-result loop computations. Calls may appear in loop bounds,
initial flags, step bodies, early exits and final results. Source semantics and
compiled closures preserve captures across every loop state. Unsupported unused
bodies are rejected even when the range is empty.

- Complete source-to-WASM proofs pass 3,397 targets and all 45 audits.
- Native Lean/V8 agree on 2,363 inputs across 114 declarations, including 78 ranges.
- All 106 prior modules retain identical bytes.
- New tests pass 9,408 comparisons, 17,664 invalid-input checks and 384 controls.
- Prior tests pass 18,816 comparisons, 35,328 invalid-input checks and 768 controls.
- All six fixed probes compile; one already compiled before the extension.
- The native corpus contains 1,723 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) records proof and test development.
Consecutive loops, nested loops, broader helper signatures and full-dialect
compiler correctness remain open.
