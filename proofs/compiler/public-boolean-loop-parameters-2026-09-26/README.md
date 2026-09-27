# Boolean public inputs in bounded loops

Candidate `9fd172aef7e63421eee98667076914820d606c0a` admits mixed UInt64/Bool public parameters through
word-valued ranges, including early exits and continue. Captured Boolean values
retain their decoded meaning across every loop state. Normalization reads stay
within the public argument slots; the emitted loop and module proofs apply.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 529 inputs across 28 declarations, including fifteen ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 8,304 native/IR comparisons and 4,032 invalid-input checks.
- Prior tests pass 154,048 comparisons, 97,920 invalid-input checks and 5,280 controls.
- The full native corpus contains 1096 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) and logs preserve the proof and test attempts. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.
Public parameter annotations, Boolean loop results, broader helper/proposition
bodies and full-dialect correctness remain subsequent work.
