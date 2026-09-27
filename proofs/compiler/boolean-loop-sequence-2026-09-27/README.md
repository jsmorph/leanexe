# Word loops with Boolean-result continuations

Candidate `c2d6f8b17ea3e80b5485e1f186e90054b25c1803` admits consecutive word-result computations followed by
a Boolean-result computation. Earlier results may supply bounds, initial flags,
loop steps, exits and final tests. Word prefixes may themselves contain several
loops. Public Boolean results encode the native flag as zero or one.

- Complete source-to-WASM proofs pass 3,418 targets and all 57 audits.
- Native Lean/V8 agree on 2,795 inputs across 132 declarations, including 96 ranges.
- All 124 prior modules retain identical bytes.
- New tests pass 14,016 comparisons, 18,432 invalid-input checks and 576 controls.
- Prior tests pass 23,424 comparisons, 36,096 invalid-input checks and 960 controls.
- All six fixed Boolean-result probes now compile.
- The native corpus contains 1,741 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) records proof and test development. Boolean-result bound
prefixes, nested loops, broader helper signatures and full-dialect compiler
correctness remain open.
