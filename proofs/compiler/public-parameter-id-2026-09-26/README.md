# Id annotations on public parameters

Candidate `6f9b106b7d3369536d8113b5b3cf86eca9560a03` admits arbitrarily nested standard Id layers on public
UInt64 and Bool parameters. Declared and lambda domains have the same base scalar
kind, and the original source application preserves input decoding. Scalar and
loop bodies reuse the existing typed binding and WASM proofs.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 499 inputs across 28 declarations, including twelve ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 105,012 native/IR comparisons, 53,376 invalid-input checks and 4,224 controls.
- Prior tests pass 105,340 comparisons, 53,568 invalid-input checks and 2,592 controls.
- The full native corpus contains 1106 declarations.

[verification.json](verification.json) records the proof and execution candidates,
commands, source hashes and modules. The compiler proof ran on `ac7598275e15ed8d7a675604e6f68761486b49d0`;
the sole subsequent correction adds UInt64 binders to native fixture adapters.
Compiler and proof sources are identical. The [journal](journal.md) and logs retain
the failed fixture attempt and its correction.

Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Boolean loop results, broader helper/proposition bodies, additional domain
metadata and full-dialect correctness remain subsequent work.
