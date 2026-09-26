# Standard Nat literal range bounds

Candidate `49c8e055` admits ordinary range bounds such as `for i in [:8]`,
alongside the existing supported UInt64 expression followed by `.toNat`.
Nat literals must use the standard OfNat instance and be smaller than 2^64.
Their independent source model retains the exact natural count. A checked
lowering lemma proves the internal UInt64 conversion cannot wrap, before
reusing the existing four-local early-exit loop and complete Wasm proofs.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial `tools/leanrun` execution:

- `tools/arithmetic-check.js proof`: complete general compiler correctness,
  module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js range-engine`: admission, reserved exports, and
  793 matching native Lean/V8 results across thirty-four range declarations.

The five new fixtures cover empty and one-step loops, a small literal bound
with break, direct constructors, and the maximum representable natural bound
with an immediate exit. Inputs include high-bit values and wrapping accumulator
arithmetic. A 2^64 bound and a custom Nat literal instance are rejected even
when their callbacks would exit immediately. The focused source-extraction test
also passed 120 native Lean/IR comparisons and both rejection tests.

All thirty-four exact modules and native expected results are retained here;
`verification.json` records sizes and SHA-256 hashes. The twenty-nine preceding
range modules are byte-for-byte unchanged. The full sixty-eight-declaration
suite is configured for 1,230 results; this increment ran the focused range
group. The fixed arithmetic archive and unrelated independent runtime/type-safety
suite were not rebuilt. Affected compiler proof dependencies, including general
type validation, were checked using cached imports.

This increment keeps zero start, unit step and one accumulator. General Nat
expressions or Nat bindings used as range bounds remain separate capabilities.
